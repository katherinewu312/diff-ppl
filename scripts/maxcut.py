#!/usr/bin/env python3
"""Benchmark forward vs reverse AD on generated weighted Max-Cut programs.

The generated program has one Bernoulli discrete variable per vertex:

  let z1 = discrete(p1, 1 - p1) in
  let z2 = discrete(p2, 1 - p2) in
  ...

and one contribution per complete-graph edge:

  let e12 = if z1 ==#2 z2 then 0.0 else 1.0 in
  ...

The objective is the weighted cut value, so differentiating the expected
objective with respect to p1, p2, ... measures the AD cost of a program with
2^n discrete assignments.

Pass --compile to add the circuit compilation backend flag to every diff_ppl
command in the benchmark run.
"""

from __future__ import annotations

import argparse
import csv
import re
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXE = REPO_ROOT / "_build" / "default" / "bin" / "main.exe"
TABLE_HEADERS = [
    "n",
    "edges",
    "expr chars",
    "function ms",
    "forward ms",
    "reverse ms",
    "fwd/function",
    "rev/function",
    "match",
]


@dataclass(frozen=True)
class CommandResult:
    elapsed_s: float
    output: str


@dataclass(frozen=True)
class Workload:
    index: int
    n: int
    values: list[str]
    program: Path
    expr_chars: int

    @property
    def edges(self) -> int:
        return self.n * (self.n - 1) // 2


@dataclass(frozen=True)
class Result:
    workload: Workload
    function_s: float
    forward_s: float
    reverse_s: float
    forward_out: str
    reverse_out: str

    @property
    def matches(self) -> bool:
        return self.forward_out == self.reverse_out


def parse_ns(text: str) -> list[int]:
    ns = []
    seen = set()
    for chunk in text.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        value = int(chunk)
        if value < 2:
            raise argparse.ArgumentTypeError("n values must be at least 2")
        if value not in seen:
            ns.append(value)
            seen.add(value)
    if not ns:
        raise argparse.ArgumentTypeError("provide at least one n value")
    return ns


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text).strip()


def format_float(value: float) -> str:
    text = f"{value:.12g}"
    return text if any(ch in text for ch in ".eE") else f"{text}.0"


def edge_name(i: int, j: int) -> str:
    if i < 10 and j < 10:
        return f"e{i}{j}"
    return f"e{i}_{j}"


def edge_weight(i: int, j: int) -> float:
    example_weights = {
        (1, 2): 1.0,
        (1, 3): 1.0,
        (2, 3): 1.0,
    }
    if (i, j) in example_weights:
        return example_weights[(i, j)]

    # Deterministic nonuniform weights, kept small to avoid noisy output.
    return 1.0 + (((37 * i + 19 * j) % 9) * 0.25)


def sum_expr(parts: list[str]) -> str:
    if not parts:
        return "0.0"
    return " + ".join(parts)


def build_maxcut_program(n: int) -> str:
    lines = []
    for i in range(1, n + 1):
        lines.append(f"let z{i} = discrete(p{i}, 1 - p{i}) in")

    edge_terms = []
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            name = edge_name(i, j)
            weight = format_float(edge_weight(i, j))
            lines.append(
                f"let {name} = if z{i} ==#2 z{j} then 0.0 else {weight} in"
            )
            edge_terms.append(name)

    lines.append(sum_expr(edge_terms))
    return "\n".join(lines)


def probability_values(n: int, probability: float) -> list[str]:
    value = format_float(probability)
    return [f"p{i}={value}" for i in range(1, n + 1)]


def build_executable(exe: Path) -> None:
    if exe.exists():
        return
    if exe != DEFAULT_EXE:
        raise FileNotFoundError(f"executable not found: {exe}")
    subprocess.run(["dune", "build", "bin/main.exe"], cwd=REPO_ROOT, check=True)


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
    elapsed_s = time.perf_counter() - start
    if completed.returncode != 0:
        raise RuntimeError(
            "command failed\n"
            f"  command: {' '.join(cmd)}\n"
            f"  stdout: {completed.stdout.strip()}\n"
            f"  stderr: {completed.stderr.strip()}"
        )
    return CommandResult(elapsed_s, strip_ansi(completed.stdout))


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
    cmd = [str(exe), *compile_args, *args, *values, str(program)]
    for _ in range(warmups):
        output = run_command(cmd, timeout_s).output

    times = []
    for _ in range(repeats):
        result = run_command(cmd, timeout_s)
        times.append(result.elapsed_s)
        output = result.output
    return statistics.median(times), output


def run_workload(
    workload: Workload,
    exe: Path,
    reverse_runtime: bool,
    repeats: int,
    warmups: int,
    timeout_s: float,
    compile_circuit: bool = False,
) -> Result:
    function_s, _ = run_repeated(
        exe,
        [],
        workload.values,
        workload.program,
        repeats,
        warmups,
        timeout_s,
        compile_circuit,
    )
    forward_s, forward_out = run_repeated(
        exe,
        ["--forward", "--ad"],
        workload.values,
        workload.program,
        repeats,
        warmups,
        timeout_s,
        compile_circuit,
    )
    reverse_s, reverse_out = run_repeated(
        exe,
        ["--reverse-runtime" if reverse_runtime else "--reverse", "--ad"],
        workload.values,
        workload.program,
        repeats,
        warmups,
        timeout_s,
        compile_circuit,
    )
    return Result(
        workload=workload,
        function_s=function_s,
        forward_s=forward_s,
        reverse_s=reverse_s,
        forward_out=forward_out,
        reverse_out=reverse_out,
    )


def format_ms(seconds: float) -> str:
    return f"{seconds * 1000.0:9.2f}"


def format_ratio(numerator: float, denominator: float) -> str:
    return f"{numerator / denominator:7.2f}x" if denominator > 0.0 else "inf"


def output_excerpt(text: str, limit: int = 240) -> str:
    single_line = " ".join(text.split())
    if len(single_line) <= limit:
        return single_line
    return single_line[: limit - 3] + "..."


def row_for_result(result: Result) -> dict[str, object]:
    workload = result.workload
    return {
        "n": workload.n,
        "edges": workload.edges,
        "expr_chars": workload.expr_chars,
        "function_ms": format_ms(result.function_s),
        "forward_ms": format_ms(result.forward_s),
        "reverse_ms": format_ms(result.reverse_s),
        "forward_over_function": format_ratio(result.forward_s, result.function_s),
        "reverse_over_function": format_ratio(result.reverse_s, result.function_s),
        "match": "yes" if result.matches else "NO",
        "function_s": result.function_s,
        "forward_s": result.forward_s,
        "reverse_s": result.reverse_s,
    }


def print_table(rows: list[dict[str, object]]) -> None:
    print("| " + " | ".join(TABLE_HEADERS) + " |")
    print("| " + " | ".join("---" for _ in TABLE_HEADERS) + " |")
    for row in rows:
        print(
            "| {n} | {edges} | {expr_chars} | {function_ms} | {forward_ms} | "
            "{reverse_ms} | {forward_over_function} | {reverse_over_function} | "
            "{match} |".format(**row)
        )


def write_csv(path: Path, rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=TABLE_HEADERS)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "n": row["n"],
                    "edges": row["edges"],
                    "expr chars": row["expr_chars"],
                    "function ms": row["function_ms"],
                    "forward ms": row["forward_ms"],
                    "reverse ms": row["reverse_ms"],
                    "fwd/function": row["forward_over_function"],
                    "rev/function": row["reverse_over_function"],
                    "match": row["match"],
                }
            )


def write_program(program_dir: Path, index: int, n: int) -> Workload:
    source = build_maxcut_program(n)
    program = program_dir / f"maxcut_{index}_n{n}.slice"
    program.write_text(source + "\n", encoding="utf-8")
    return Workload(
        index=index,
        n=n,
        values=[],
        program=program,
        expr_chars=len(source),
    )


def make_workloads(
    ns: list[int],
    probability: float,
    program_dir: Path,
) -> list[Workload]:
    workloads = []
    for index, n in enumerate(ns):
        workload = write_program(program_dir, index, n)
        workloads.append(
            Workload(
                index=workload.index,
                n=workload.n,
                values=probability_values(n, probability),
                program=workload.program,
                expr_chars=workload.expr_chars,
            )
        )
    return workloads


def execute_workloads(
    workloads: list[Workload],
    exe: Path,
    reverse_runtime: bool,
    repeats: int,
    warmups: int,
    timeout_s: float,
    jobs: int,
    compile_circuit: bool = False,
) -> list[Result]:
    def run(workload: Workload) -> Result:
        return run_workload(
            workload,
            exe,
            reverse_runtime,
            repeats,
            warmups,
            timeout_s,
            compile_circuit,
        )

    if jobs == 1:
        return [run(workload) for workload in workloads]

    results = []
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {executor.submit(run, workload): workload for workload in workloads}
        completed = 0
        for future in as_completed(futures):
            workload = futures[future]
            results.append(future.result())
            completed += 1
            print(
                f"Completed {completed}/{len(workloads)}: n={workload.n}",
                file=sys.stderr,
                flush=True,
            )
    return sorted(results, key=lambda result: result.workload.index)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Benchmark forward vs reverse AD on generated Max-Cut programs."
    )
    parser.add_argument(
        "--n",
        type=int,
        help="single vertex count to test",
    )
    parser.add_argument(
        "--ns",
        type=parse_ns,
        help="comma-separated vertex counts to test (default: 3,4,5,6)",
    )
    parser.add_argument(
        "--probability",
        type=float,
        default=0.35,
        help="probability assigned to every p_i (default: 0.35)",
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="prepend --compile to every diff_ppl command",
    )
    parser.add_argument(
        "--reverse-runtime",
        action="store_true",
        help="time concrete --reverse-runtime --ad instead of symbolic --reverse --ad",
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
        help="timeout in seconds for one command (default: 600)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="number of independent n workloads to run concurrently (default: 1)",
    )
    parser.add_argument(
        "--exe",
        type=Path,
        default=DEFAULT_EXE,
        help=f"diff_ppl executable path (default: {DEFAULT_EXE})",
    )
    parser.add_argument(
        "--keep-programs",
        type=Path,
        help="write generated .slice files to this directory instead of a temporary directory",
    )
    parser.add_argument(
        "--csv",
        type=Path,
        default=REPO_ROOT / "results_maxcut.csv",
        help="write results to this CSV path (default: results_maxcut.csv)",
    )
    parser.add_argument(
        "--show-sample",
        action="store_true",
        help="print one forward/reverse output sample",
    )
    args = parser.parse_args()

    if args.n is not None and args.ns is not None:
        parser.error("use either --n or --ns, not both")
    if args.n is not None and args.n < 2:
        parser.error("--n must be at least 2")
    if args.repeats <= 0:
        parser.error("--repeats must be positive")
    if args.warmups < 0:
        parser.error("--warmups cannot be negative")
    if args.jobs <= 0:
        parser.error("--jobs must be positive")
    if not 0.0 <= args.probability <= 1.0:
        parser.error("--probability must be between 0 and 1")

    ns = [args.n] if args.n is not None else (args.ns or parse_ns("3,4,5,6"))
    build_executable(args.exe)

    rows: list[dict[str, object]] = []
    mismatches = 0
    sample: tuple[int, str, str] | None = None

    def run_all(program_dir: Path) -> None:
        nonlocal mismatches, sample
        workloads = make_workloads(ns, args.probability, program_dir)
        results = execute_workloads(
            workloads,
            args.exe,
            args.reverse_runtime,
            args.repeats,
            args.warmups,
            args.timeout,
            args.jobs,
            args.compile,
        )

        for result in results:
            if not result.matches:
                mismatches += 1
                print(
                    f"\nMismatch for n={result.workload.n}\n"
                    f"  forward: {output_excerpt(result.forward_out)}\n"
                    f"  reverse: {output_excerpt(result.reverse_out)}\n",
                    file=sys.stderr,
                )
            if args.show_sample and sample is None:
                sample = (
                    result.workload.n,
                    result.forward_out,
                    result.reverse_out,
                )
            rows.append(row_for_result(result))

    if args.keep_programs:
        args.keep_programs.mkdir(parents=True, exist_ok=True)
        run_all(args.keep_programs)
        print(f"Generated programs: {args.keep_programs}")
    else:
        with tempfile.TemporaryDirectory(prefix="diff-ppl-maxcut-") as tmp:
            run_all(Path(tmp))

    print()
    print(
        f"Max-Cut AD benchmark; repeats: {args.repeats}; "
        f"warmups: {args.warmups}; "
        f"reverse: {'runtime' if args.reverse_runtime else 'symbolic'}; "
        f"p_i: {format_float(args.probability)}; jobs: {args.jobs}"
    )
    print_table(rows)

    if sample:
        n, forward_out, reverse_out = sample
        print()
        print(f"Output sample for n={n}")
        print(f"  forward: {output_excerpt(forward_out)}")
        print(f"  reverse: {output_excerpt(reverse_out)}")

    write_csv(args.csv, rows)
    print(f"\nCSV results: {args.csv}")

    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
