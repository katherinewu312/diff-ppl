#!/usr/bin/env python3
"""Benchmark forward vs reverse AD gradient scaling.

The script generates 5 scalar output programs:

  dense_linear_sum:       x1 + x2 + ... + xn
  dense_quadratic_sum:    x1*x1 + x2*x2 + ... + xn*xn
  dense_coupled_square:   let s = x1 + ... + xn in s*s
  probabilistic_branch:   E[if discrete(p, 1-p) then sum(xs) else sumsq(xs)]
  discrete_chain:         nested discrete choices:
                            let b1 = discrete(p, 1 - p) in
                            let s1 = if b1 <#2 1#2 then x1 else x1 * x1 in
                            let b2 = discrete(p, 1 - p) in
                            let s2 = if b2 <#2 1#2 then s1 + x2 else s1 * x2 in
                            ...
                            let sn = if bn <#2 1#2 then s(n-1) + xn else s(n-1) * xn in
                            sn

For each program and size n, it times expectation evaluation plus the requested
full-gradient AD modes:

  diff_ppl --expect ...
  diff_ppl --forward --ad ...
  diff_ppl --reverse --ad ...

It strips ANSI color codes before comparing the outputs, then reports median
wall-clock time and AD/function runtime ratios over the requested number of
repeats.

For each family, it writes a log-scale forward/reverse timing plot to the
results/ directory.

Use --modes forward,reverse to choose which AD modes to time. Use --jobs N to
run independent family/size workloads concurrently. Each workload still runs
its requested function/AD timings sequentially.

It writes table-shaped CSV results to results/results_symbolic.csv by default,
or results/results_concrete.csv when --reverse-runtime is used.
The table's enumerated-branches column contains the naive path count normally,
or the factorized after-compilation count when --compile is used.

Pass --compile to add the circuit compilation backend flag to every diff_ppl
command in the benchmark run.

Usage:
$ python3 benchmark.py [-h] [--ns NS] [--families FAMILIES] [--ad-output {ad,ad-dual}] [--modes MODES] [--compile] [--reverse-runtime] [--repeats REPEATS] [--warmups WARMUPS] [--timeout TIMEOUT] [--jobs JOBS] [--keep-programs KEEP_PROGRAMS]
                    [--csv CSV] [--show-samples]
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Optional


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXE = REPO_ROOT / "_build" / "default" / "bin" / "main.exe"
RESULTS_DIR = REPO_ROOT / "results"
TABLE_HEADERS = [
    "family",
    "n",
    "enumerated branches",
    "function ms",
    "forward ms",
    "reverse ms",
    "fwd/function",
    "rev/function",
    "match",
]


@dataclass(frozen=True)
class Family:
    name: str
    description: str
    build: Callable[[list[str]], str]
    uses_probability_param: bool = False


@dataclass
class CommandResult:
    elapsed_s: float
    output: str


@dataclass(frozen=True)
class BenchmarkWorkload:
    index: int
    family_name: str
    n: int
    values: list[str]
    program: Path


@dataclass
class BenchmarkResult:
    workload: BenchmarkWorkload
    enumerated_branches: int
    function_s: float
    forward_s: Optional[float]
    reverse_s: Optional[float]
    forward_out: Optional[str]
    reverse_out: Optional[str]

    @property
    def matches(self) -> Optional[bool]:
        if self.forward_out is None or self.reverse_out is None:
            return None
        return self.forward_out == self.reverse_out


def sum_expr(parts: Iterable[str]) -> str:
    return " + ".join(parts)


def dense_linear_sum(vars_: list[str]) -> str:
    return sum_expr(vars_)


def dense_quadratic_sum(vars_: list[str]) -> str:
    return sum_expr(f"{x} * {x}" for x in vars_)


def dense_coupled_square(vars_: list[str]) -> str:
    return f"let s = {sum_expr(vars_)} in s * s"


def probabilistic_branch(vars_: list[str]) -> str:
    linear = sum_expr(vars_)
    quadratic = dense_quadratic_sum(vars_)
    return (
        "let b = discrete(p, 1 - p) in "
        f"if b <#2 1#2 then {linear} else {quadratic}"
    )


def discrete_chain(vars_: list[str]) -> str:
    bindings = []
    for i, x in enumerate(vars_, 1):
        b = f"b{i}"
        s = f"s{i}"
        then_expr = x if i == 1 else f"s{i - 1} + {x}"
        else_expr = f"{x} * {x}" if i == 1 else f"s{i - 1} * {x}"
        bindings.append(f"let {b} = discrete(p, 1 - p) in")
        bindings.append(
            f"let {s} = if {b} <#2 1#2 then {then_expr} else {else_expr} in"
        )
    return "\n".join([*bindings, f"s{len(vars_)}"])


FAMILIES = {
    family.name: family
    for family in [
        Family(
            "dense_linear_sum",
            "x1 + x2 + ... + xn",
            dense_linear_sum,
        ),
        Family(
            "dense_quadratic_sum",
            "x1*x1 + x2*x2 + ... + xn*xn",
            dense_quadratic_sum,
        ),
        Family(
            "dense_coupled_square",
            "let s = x1 + ... + xn in s*s",
            dense_coupled_square,
        ),
        Family(
            "probabilistic_branch",
            "if discrete(p, 1-p) then sum(xs) else sumsq(xs)",
            probabilistic_branch,
            uses_probability_param=True,
        ),
        Family(
            "discrete_chain",
            "nested discrete choices",
            discrete_chain,
            uses_probability_param=True,
        ),
    ]
}


def parse_ns(text: str) -> list[int]:
    ns = []
    for chunk in text.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        value = int(chunk)
        if value <= 0:
            raise argparse.ArgumentTypeError("n values must be positive")
        ns.append(value)
    if not ns:
        raise argparse.ArgumentTypeError("provide at least one n value")
    return ns


def parse_families(text: str) -> list[str]:
    names = [chunk.strip() for chunk in text.split(",") if chunk.strip()]
    unknown = [name for name in names if name not in FAMILIES]
    if unknown:
        known = ", ".join(FAMILIES)
        raise argparse.ArgumentTypeError(
            f"unknown families: {', '.join(unknown)}; known: {known}"
        )
    return names


def parse_modes(text: str) -> list[str]:
    modes = []
    valid = {"forward", "reverse", "both"}
    for chunk in text.split(","):
        mode = chunk.strip().lower()
        if not mode:
            continue
        if mode not in valid:
            raise argparse.ArgumentTypeError(
                "modes must be forward, reverse, or both"
            )
        expanded = ["forward", "reverse"] if mode == "both" else [mode]
        for item in expanded:
            if item not in modes:
                modes.append(item)
    if not modes:
        raise argparse.ArgumentTypeError("provide at least one AD mode")
    return modes


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text).strip()


def variable_names(n: int, width: int) -> list[str]:
    return [f"x{i:0{width}d}" for i in range(1, n + 1)]


def assignments(vars_: list[str]) -> list[str]:
    n = len(vars_)
    # Use distinct positive values. Keeping them small makes large polynomial
    # outputs readable and avoids unnecessarily large constants after folding.
    return [f"{name}={0.1 + (i / (10.0 * max(1, n))):.12g}" for i, name in enumerate(vars_, 1)]


def one_assignments(vars_: list[str]) -> list[str]:
    return [f"{name}=1" for name in vars_]


def family_assignments(family: Family, vars_: list[str]) -> list[str]:
    values = assignments(vars_)
    if family.uses_probability_param:
        return ["p=0.35", *values]
    return values


def family_one_assignments(family: Family, vars_: list[str]) -> list[str]:
    values = one_assignments(vars_)
    if family.uses_probability_param:
        return ["p=1", *values]
    return values


def build_executable(exe: Path) -> None:
    if exe.exists():
        return
    subprocess.run(
        ["dune", "build", "bin/main.exe"],
        cwd=REPO_ROOT,
        check=True,
    )


def run_command(cmd: list[str], timeout_s: float) -> CommandResult:
    start = time.perf_counter()
    completed = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_s,
    )
    elapsed = time.perf_counter() - start
    if completed.returncode != 0:
        raise RuntimeError(
            "command failed\n"
            f"  command: {' '.join(cmd)}\n"
            f"  stdout: {completed.stdout.strip()}\n"
            f"  stderr: {completed.stderr.strip()}"
        )
    return CommandResult(elapsed, strip_ansi(completed.stdout))


def run_diff_ppl(
    exe: Path,
    args: list[str],
    timeout_s: float,
) -> CommandResult:
    return run_command([str(exe), *args], timeout_s)


def count_enumerated_branches(
    exe: Path,
    values: list[str],
    program: Path,
    timeout_s: float,
    compile_circuit: bool,
) -> int:
    compile_args = ["--compile"] if compile_circuit else []
    result = run_diff_ppl(
        exe,
        [*compile_args, "--enumerated-paths", *values, str(program)],
        timeout_s,
    )
    try:
        return int(result.output)
    except ValueError as exc:
        raise RuntimeError(
            f"could not parse enumerated branch count from: {result.output!r}"
        ) from exc


def run_repeated(
    exe: Path,
    args: list[str],
    values: list[str],
    program: Path,
    repeats: int,
    warmups: int,
    timeout_s: float,
    compile_circuit: bool = False,
) -> tuple[float, str]:
    output = ""
    compile_args = ["--compile"] if compile_circuit else []
    cmd_args = [*compile_args, *args, *values, str(program)]
    for _ in range(warmups):
        output = run_diff_ppl(exe, cmd_args, timeout_s).output

    times = []
    for _ in range(repeats):
        result = run_diff_ppl(exe, cmd_args, timeout_s)
        times.append(result.elapsed_s)
        output = result.output
    return statistics.median(times), output


def write_program(root: Path, family: Family, n: int, vars_: list[str]) -> Path:
    path = root / f"{family.name}_{n}.slice"
    path.write_text(family.build(vars_) + "\n", encoding="utf-8")
    return path


def run_benchmark_workload(
    workload: BenchmarkWorkload,
    exe: Path,
    ad_output: str,
    modes: list[str],
    reverse_runtime: bool,
    repeats: int,
    warmups: int,
    timeout_s: float,
    compile_circuit: bool = False,
) -> BenchmarkResult:
    enumerated_branches = count_enumerated_branches(
        exe,
        workload.values,
        workload.program,
        timeout_s,
        compile_circuit,
    )
    function_s, _ = run_repeated(
        exe,
        ["--expect"],
        workload.values,
        workload.program,
        repeats,
        warmups,
        timeout_s,
        compile_circuit,
    )
    forward_s = None
    forward_out = None
    if "forward" in modes:
        forward_s, forward_out = run_repeated(
            exe,
            ["--forward", f"--{ad_output}"],
            workload.values,
            workload.program,
            repeats,
            warmups,
            timeout_s,
            compile_circuit,
        )

    reverse_s = None
    reverse_out = None
    if "reverse" in modes:
        reverse_s, reverse_out = run_repeated(
            exe,
            [
                "--reverse-runtime" if reverse_runtime else "--reverse",
                f"--{ad_output}",
            ],
            workload.values,
            workload.program,
            repeats,
            warmups,
            timeout_s,
            compile_circuit,
        )
    return BenchmarkResult(
        workload=workload,
        enumerated_branches=enumerated_branches,
        function_s=function_s,
        forward_s=forward_s,
        reverse_s=reverse_s,
        forward_out=forward_out,
        reverse_out=reverse_out,
    )


def format_ms(seconds: float) -> str:
    return f"{seconds * 1000.0:9.2f}"


def format_optional_ms(seconds: Optional[float]) -> str:
    return "--" if seconds is None else format_ms(seconds)


def format_ratio(numerator: float, denominator: float) -> str:
    return f"{numerator / denominator:7.2f}x" if denominator > 0.0 else "inf"


def format_optional_ratio(numerator: Optional[float], denominator: float) -> str:
    if numerator is None:
        return "--"
    return format_ratio(numerator, denominator)


def format_match(result: BenchmarkResult) -> str:
    matches = result.matches
    if matches is None:
        return "skipped"
    return "yes" if matches else "NO"


def output_excerpt(text: str, limit: int = 240) -> str:
    single_line = " ".join(text.split())
    if len(single_line) <= limit:
        return single_line
    return single_line[: limit - 3] + "..."


def print_table(rows: list[dict[str, object]]) -> None:
    print("| " + " | ".join(TABLE_HEADERS) + " |")
    print("| " + " | ".join("---" for _ in TABLE_HEADERS) + " |")
    for row in rows:
        print(
            "| {family} | {n} | {enumerated_branches} | {function_ms} | {forward_ms} | "
            "{reverse_ms} | {forward_over_function} | {reverse_over_function} | "
            "{match} |".format(**row)
        )


def table_csv_path(reverse_runtime: bool) -> Path:
    name = "results_concrete.csv" if reverse_runtime else "results_symbolic.csv"
    return RESULTS_DIR / name


def write_table_csv(path: Path, rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=TABLE_HEADERS)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "family": row["family"],
                    "n": row["n"],
                    "enumerated branches": row["enumerated_branches"],
                    "function ms": row["function_ms"],
                    "forward ms": row["forward_ms"],
                    "reverse ms": row["reverse_ms"],
                    "fwd/function": row["forward_over_function"],
                    "rev/function": row["reverse_over_function"],
                    "match": row["match"],
                }
            )


def plot_family_times(family: Family, rows: list[dict[str, object]]) -> Path:
    try:
        mpl_cache = Path(tempfile.gettempdir()) / "diff-ppl-matplotlib"
        mpl_cache.mkdir(parents=True, exist_ok=True)
        os.environ.setdefault("MPLCONFIGDIR", str(mpl_cache))

        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.ticker import ScalarFormatter
    except ImportError as exc:
        raise RuntimeError(
            "matplotlib is required to generate benchmark graphs"
        ) from exc

    ns = [int(row["n"]) for row in rows]
    function_ms = [float(row["function_s"]) * 1000.0 for row in rows]

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(ns, function_ms, marker="o", color="tab:green", label="function")
    forward_points = [
        (int(row["n"]), float(row["forward_s"]) * 1000.0)
        for row in rows
        if row["forward_s"] is not None
    ]
    if forward_points:
        forward_ns, forward_ms = zip(*forward_points)
        ax.plot(forward_ns, forward_ms, marker="o", color="tab:blue", label="forward")
    reverse_points = [
        (int(row["n"]), float(row["reverse_s"]) * 1000.0)
        for row in rows
        if row["reverse_s"] is not None
    ]
    if reverse_points:
        reverse_ns, reverse_ms = zip(*reverse_points)
        ax.plot(reverse_ns, reverse_ms, marker="o", color="tab:orange", label="reverse")
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlabel("n")
    ax.set_ylabel("time (ms)")
    ax.set_title(f"{family.name}: function vs forward vs reverse time")
    ax.set_xticks(ns)
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.grid(True, which="both", linestyle=":", linewidth=0.7)
    ax.legend()
    fig.tight_layout()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    path = RESULTS_DIR / f"benchmark_{family.name}.png"
    fig.savefig(path, dpi=160)
    plt.close(fig)
    return path


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Benchmark forward vs reverse AD on generated programs."
    )
    parser.add_argument(
        "--ns",
        type=parse_ns,
        default=parse_ns("1,2,4,8,16,32,64"),
        help="comma-separated sizes to test (default: 1,2,4,8,16,32,64)",
    )
    parser.add_argument(
        "--families",
        type=parse_families,
        default=list(FAMILIES),
        help="comma-separated families to test (default: all)",
    )
    parser.add_argument(
        "--ad-output",
        choices=["ad", "ad-dual"],
        default="ad",
        help="compare --ad or --ad-dual output (default: ad)",
    )
    parser.add_argument(
        "--modes",
        type=parse_modes,
        default=parse_modes("forward,reverse"),
        help=(
            "comma-separated AD modes to time: forward, reverse, or both "
            "(default: forward,reverse)"
        ),
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="prepend --compile to every diff_ppl command",
    )
    parser.add_argument(
        "--reverse-runtime",
        action="store_true",
        help="time the concrete --reverse-runtime --ad path instead of symbolic --reverse --ad",
    )
    parser.add_argument(
        "--repeats",
        type=int,
        default=3,
        help="timed repeats per mode/program (default: 3)",
    )
    parser.add_argument(
        "--warmups",
        type=int,
        default=1,
        help="untimed warmups per mode/program (default: 1)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=600.0,
        help="timeout in seconds for one benchmark command (default: 600)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="number of independent family/size workloads to run concurrently (default: 1)",
    )
    parser.add_argument(
        "--keep-programs",
        type=Path,
        help="write generated .slice files to this directory instead of a temporary directory",
    )
    parser.add_argument(
        "--csv",
        type=Path,
        help=(
            "write table-shaped results to this CSV path "
            "(default: results/results_symbolic.csv, or "
            "results/results_concrete.csv with --reverse-runtime)"
        ),
    )
    parser.add_argument(
        "--show-samples",
        action="store_true",
        help="print one forward/reverse output sample per family",
    )
    args = parser.parse_args()

    if args.repeats <= 0:
        parser.error("--repeats must be positive")
    if args.warmups < 0:
        parser.error("--warmups cannot be negative")
    if args.jobs <= 0:
        parser.error("--jobs must be positive")
    if args.reverse_runtime and "reverse" in args.modes and args.ad_output != "ad":
        parser.error("--reverse-runtime currently supports only --ad output")

    use_reverse_runtime = args.reverse_runtime and "reverse" in args.modes
    build_executable(DEFAULT_EXE)

    max_n = max(args.ns)
    width = max(3, len(str(max_n)))
    rows: list[dict[str, object]] = []
    samples: list[tuple[str, int, Optional[str], Optional[str]]] = []
    mismatches = 0

    def make_workloads(program_dir: Path) -> list[BenchmarkWorkload]:
        workloads = []
        for family_name in args.families:
            family = FAMILIES[family_name]
            for n in args.ns:
                vars_ = variable_names(n, width)
                values = (
                    family_one_assignments(family, vars_)
                    if use_reverse_runtime
                    else family_assignments(family, vars_)
                )
                program = write_program(program_dir, family, n, vars_)
                workloads.append(
                    BenchmarkWorkload(
                        index=len(workloads),
                        family_name=family.name,
                        n=n,
                        values=values,
                        program=program,
                    )
                )
        return workloads

    def execute_workloads(workloads: list[BenchmarkWorkload]) -> list[BenchmarkResult]:
        def run(workload: BenchmarkWorkload) -> BenchmarkResult:
            return run_benchmark_workload(
                workload,
                DEFAULT_EXE,
                args.ad_output,
                args.modes,
                use_reverse_runtime,
                args.repeats,
                args.warmups,
                args.timeout,
                args.compile,
            )

        if args.jobs == 1:
            return [run(workload) for workload in workloads]

        results = []
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {
                executor.submit(run, workload): workload for workload in workloads
            }
            completed = 0
            for future in as_completed(futures):
                workload = futures[future]
                results.append(future.result())
                completed += 1
                print(
                    f"Completed {completed}/{len(workloads)}: "
                    f"{workload.family_name}, n={workload.n}",
                    file=sys.stderr,
                    flush=True,
                )
        return sorted(results, key=lambda result: result.workload.index)

    def run_all(program_dir: Path) -> None:
        nonlocal mismatches
        workloads = make_workloads(program_dir)
        results = execute_workloads(workloads)
        sampled_families: set[str] = set()

        for result in results:
            workload = result.workload
            if result.matches is False:
                mismatches += 1
                print(
                    f"\nMismatch for {workload.family_name}, n={workload.n}\n"
                    f"  forward: {output_excerpt(result.forward_out)}\n"
                    f"  reverse: {output_excerpt(result.reverse_out)}\n",
                    file=sys.stderr,
                )

            rows.append(
                {
                    "family": workload.family_name,
                    "n": workload.n,
                    "enumerated_branches": result.enumerated_branches,
                    "function_ms": format_ms(result.function_s),
                    "forward_ms": format_optional_ms(result.forward_s),
                    "reverse_ms": format_optional_ms(result.reverse_s),
                    "forward_over_function": format_optional_ratio(
                        result.forward_s, result.function_s
                    ),
                    "reverse_over_function": format_optional_ratio(
                        result.reverse_s, result.function_s
                    ),
                    "match": format_match(result),
                    "function_s": result.function_s,
                    "forward_s": result.forward_s,
                    "reverse_s": result.reverse_s,
                }
            )

            if args.show_samples and workload.family_name not in sampled_families:
                samples.append(
                    (
                        workload.family_name,
                        workload.n,
                        result.forward_out,
                        result.reverse_out,
                    )
                )
                sampled_families.add(workload.family_name)

        for family_name in args.families:
            family = FAMILIES[family_name]
            family_rows = [row for row in rows if row["family"] == family.name]
            graph_path = plot_family_times(family, family_rows)
            print(f"Graph: {graph_path}")

    if args.keep_programs:
        args.keep_programs.mkdir(parents=True, exist_ok=True)
        run_all(args.keep_programs)
        print(f"Generated programs: {args.keep_programs}")
    else:
        with tempfile.TemporaryDirectory(prefix="diff-ppl-ad-bench-") as tmp:
            run_all(Path(tmp))

    print()
    reverse_label = (
        "skipped"
        if "reverse" not in args.modes
        else "runtime" if use_reverse_runtime else "symbolic"
    )
    print(
        f"AD output: --{args.ad_output}; repeats: {args.repeats}; "
        f"warmups: {args.warmups}; "
        f"modes: {','.join(args.modes)}; "
        f"reverse: {reverse_label}; "
        f"jobs: {args.jobs}"
    )
    print_table(rows)

    if samples:
        print()
        print("Output samples")
        for family, n, forward_out, reverse_out in samples:
            print(f"- {family}, n={n}")
            if forward_out is None:
                print("  forward: skipped")
            else:
                print(f"  forward: {output_excerpt(forward_out)}")
            if reverse_out is None:
                print("  reverse: skipped")
            else:
                print(f"  reverse: {output_excerpt(reverse_out)}")

    csv_path = args.csv if args.csv else table_csv_path(use_reverse_runtime)
    write_table_csv(csv_path, rows)
    print(f"\nCSV results: {csv_path}")

    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
