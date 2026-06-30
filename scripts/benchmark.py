#!/usr/bin/env python3
"""Benchmark forward vs reverse AD gradient scaling.

The script generates 4 scalar output programs:

  dense_linear_sum:       x1 + x2 + ... + xn
  dense_quadratic_sum:    x1*x1 + x2*x2 + ... + xn*xn
  dense_coupled_square:   let s = x1 + ... + xn in s*s
  probabilistic_branch:   E[if discrete(p, 1-p) then sum(xs) else sumsq(xs)]

For each program and size n, it runs both no-explicit-seed AD modes:

  diff_ppl --forward --ad ...
  diff_ppl --reverse --ad ...

It strips ANSI color codes before comparing the outputs, then reports median
wall-clock time over the requested number of repeats.
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
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXE = REPO_ROOT / "_build" / "default" / "bin" / "main.exe"


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


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text).strip()


def variable_names(n: int, width: int) -> list[str]:
    return [f"x{i:0{width}d}" for i in range(1, n + 1)]


def assignments(vars_: list[str]) -> list[str]:
    n = len(vars_)
    # Use distinct positive values. Keeping them small makes large polynomial
    # outputs readable and avoids unnecessarily large constants after folding.
    return [f"{name}={0.1 + (i / (10.0 * max(1, n))):.12g}" for i, name in enumerate(vars_, 1)]


def family_assignments(family: Family, vars_: list[str]) -> list[str]:
    values = assignments(vars_)
    if family.uses_probability_param:
        return ["p=0.35", *values]
    return values


def build_executable(exe: Path) -> None:
    if exe.exists():
        return
    subprocess.run(
        ["dune", "build", "bin/main.exe"],
        cwd=REPO_ROOT,
        check=True,
    )


def run_diff_ppl(
    exe: Path,
    mode: str,
    ad_flag: str,
    values: list[str],
    program: Path,
    timeout_s: float,
) -> CommandResult:
    cmd = [str(exe), f"--{mode}", f"--{ad_flag}", *values, str(program)]
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


def run_repeated(
    exe: Path,
    mode: str,
    ad_flag: str,
    values: list[str],
    program: Path,
    repeats: int,
    warmups: int,
    timeout_s: float,
) -> tuple[float, str]:
    output = ""
    for _ in range(warmups):
        output = run_diff_ppl(exe, mode, ad_flag, values, program, timeout_s).output

    times = []
    for _ in range(repeats):
        result = run_diff_ppl(exe, mode, ad_flag, values, program, timeout_s)
        times.append(result.elapsed_s)
        output = result.output
    return statistics.median(times), output


def write_program(root: Path, family: Family, n: int, vars_: list[str]) -> Path:
    path = root / f"{family.name}_{n}.slice"
    path.write_text(family.build(vars_) + "\n", encoding="utf-8")
    return path


def format_ms(seconds: float) -> str:
    return f"{seconds * 1000.0:9.2f}"


def output_excerpt(text: str, limit: int = 240) -> str:
    single_line = " ".join(text.split())
    if len(single_line) <= limit:
        return single_line
    return single_line[: limit - 3] + "..."


def print_table(rows: list[dict[str, object]]) -> None:
    headers = [
        "family",
        "n",
        "expr chars",
        "forward ms",
        "reverse ms",
        "fwd/rev",
        "match",
    ]
    print("| " + " | ".join(headers) + " |")
    print("| " + " | ".join("---" for _ in headers) + " |")
    for row in rows:
        print(
            "| {family} | {n} | {expr_chars} | {forward_ms} | {reverse_ms} | "
            "{speedup} | {match} |".format(**row)
        )


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
        default=120.0,
        help="timeout in seconds for one AD command (default: 120)",
    )
    parser.add_argument(
        "--keep-programs",
        type=Path,
        help="write generated .slice files to this directory instead of a temporary directory",
    )
    parser.add_argument(
        "--csv",
        type=Path,
        help="also write machine-readable results to this CSV path",
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

    build_executable(DEFAULT_EXE)

    max_n = max(args.ns)
    width = max(3, len(str(max_n)))
    rows: list[dict[str, object]] = []
    samples: list[tuple[str, int, str, str]] = []
    mismatches = 0

    def run_all(program_dir: Path) -> None:
        nonlocal mismatches
        for family_name in args.families:
            family = FAMILIES[family_name]
            sample_recorded = False
            for n in args.ns:
                vars_ = variable_names(n, width)
                values = family_assignments(family, vars_)
                program = write_program(program_dir, family, n, vars_)
                expr_chars = len(program.read_text(encoding="utf-8").strip())

                forward_s, forward_out = run_repeated(
                    DEFAULT_EXE,
                    "forward",
                    args.ad_output,
                    values,
                    program,
                    args.repeats,
                    args.warmups,
                    args.timeout,
                )
                reverse_s, reverse_out = run_repeated(
                    DEFAULT_EXE,
                    "reverse",
                    args.ad_output,
                    values,
                    program,
                    args.repeats,
                    args.warmups,
                    args.timeout,
                )

                matches = forward_out == reverse_out
                if not matches:
                    mismatches += 1
                    print(
                        f"\nMismatch for {family.name}, n={n}\n"
                        f"  forward: {output_excerpt(forward_out)}\n"
                        f"  reverse: {output_excerpt(reverse_out)}\n",
                        file=sys.stderr,
                    )

                rows.append(
                    {
                        "family": family.name,
                        "n": n,
                        "expr_chars": expr_chars,
                        "forward_ms": format_ms(forward_s),
                        "reverse_ms": format_ms(reverse_s),
                        "speedup": f"{forward_s / reverse_s:7.2f}x"
                        if reverse_s > 0.0
                        else "inf",
                        "match": "yes" if matches else "NO",
                        "forward_s": forward_s,
                        "reverse_s": reverse_s,
                    }
                )

                if args.show_samples and not sample_recorded:
                    samples.append((family.name, n, forward_out, reverse_out))
                    sample_recorded = True

    if args.keep_programs:
        args.keep_programs.mkdir(parents=True, exist_ok=True)
        run_all(args.keep_programs)
        print(f"Generated programs: {args.keep_programs}")
    else:
        with tempfile.TemporaryDirectory(prefix="diff-ppl-ad-bench-") as tmp:
            run_all(Path(tmp))

    print()
    print(
        f"AD output: --{args.ad_output}; repeats: {args.repeats}; "
        f"warmups: {args.warmups}"
    )
    print_table(rows)

    if samples:
        print()
        print("Output samples")
        for family, n, forward_out, reverse_out in samples:
            print(f"- {family}, n={n}")
            print(f"  forward: {output_excerpt(forward_out)}")
            print(f"  reverse: {output_excerpt(reverse_out)}")

    if args.csv:
        with args.csv.open("w", newline="", encoding="utf-8") as csv_file:
            writer = csv.DictWriter(
                csv_file,
                fieldnames=[
                    "family",
                    "n",
                    "expr_chars",
                    "forward_s",
                    "reverse_s",
                    "speedup",
                    "match",
                ],
            )
            writer.writeheader()
            for row in rows:
                writer.writerow(
                    {
                        "family": row["family"],
                        "n": row["n"],
                        "expr_chars": row["expr_chars"],
                        "forward_s": f"{row['forward_s']:.9f}",
                        "reverse_s": f"{row['reverse_s']:.9f}",
                        "speedup": row["speedup"],
                        "match": row["match"],
                    }
                )
        print(f"\nCSV results: {args.csv}")

    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
