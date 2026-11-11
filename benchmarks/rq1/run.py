#!/usr/bin/env python3
"""Run the boundary-analysis suite; requires dune and z3, no Python packages."""

import argparse
import collections
import csv
import json
import statistics
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

SUITE = Path(__file__).resolve().parent
ROOT = SUITE.parent.parent
ANALYZER = ROOT / "_build/default/bin/main.exe"
RESULTS = SUITE / "results"
STATUSES = ("sat", "unsat", "redundant", "unknown")
PROGRAM_ORDER = ("threshold", "cancellation", "gated", "piecewise",
                 "infeasible", "coincident", "crossing", "kinks")


def expression(value):
    """Render analyzer expressions without approximating exact constants."""
    kind = value["kind"]
    if kind == "number":
        return str(Fraction(value["exact"].strip("()")))
    if kind == "sample":
        return "s" + str(value["id"])
    if kind == "parameter":
        return value["name"]
    if kind == "boolean" and "value" in value:
        return str(value["value"]).lower()
    if kind == "not":
        return "not " + expression(value["operand"])
    if kind == "ite":
        return "ite(" + ", ".join(expression(value[key])
                                   for key in ("condition", "then", "else")) + ")"
    if kind in ("arithmetic", "comparison", "boolean"):
        return f"({expression(value['left'])} {value['op']} {expression(value['right'])})"
    raise ValueError("Unsupported boundary expression: " + kind)


def print_boundaries(candidates, mode):
    selected = [(index, b) for index, b in enumerate(candidates, 1)
                if mode == "all" or b["retained"]]
    if not selected:
        print("  Retained boundaries: none")
    for index, boundary in selected:
        state = "retained" if boundary["retained"] else "dropped"
        print(f"  B{index}: {expression(boundary['guard'])} = 0 "
              f"[{boundary['solver'].upper()}, {state}]")
        print("      path: " + expression(boundary["path"]))
        region = boundary.get("integration_region")
        if boundary["retained"]:
            print("      assigned surface region: " +
                  (expression(region) if region is not None else "unresolved"))
        if boundary.get("reason"):
            print("      reason: " + boundary["reason"])


def analyze(program, theta, args):
    command = [str(ANALYZER), "--json", "--solver-timeout-ms",
               str(args.solver_timeout_ms)]
    if theta is not None:
        command += ["--at", "theta=" + theta]
    command.append(str(program))
    durations, summary = [], None
    for index in range(args.warmups + args.runs):
        start = time.perf_counter()
        result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                text=True, timeout=args.timeout)
        duration = time.perf_counter() - start
        if result.returncode:
            raise ValueError(result.stderr.strip() or "Analyzer failed")
        report = json.loads(result.stdout)
        if report.get("schema_version") != 5:
            raise ValueError("Expected analyzer JSON schema 5")
        candidates = report["candidates"]
        counts = collections.Counter(b["solver"] for b in candidates)
        if set(counts) - set(STATUSES):
            raise ValueError("Unrecognized solver status")
        retained = sum(b["retained"] for b in candidates)
        if retained != counts["sat"] + counts["unknown"]:
            raise ValueError("Inconsistent retained-record count")
        if retained != report["retained_count"]:
            raise ValueError("Inconsistent report summary")
        current = {"extracted": len(candidates), "retained": retained,
                   **{status: counts[status] for status in STATUSES}}
        if index >= args.warmups:
            if summary is not None and current != summary:
                raise ValueError("Boundary counts changed between measured runs")
            summary = current
            durations.append(duration)
    return ({**summary, "time_s": statistics.median(durations),
             "min_s": min(durations), "max_s": max(durations)}, candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", nargs="+", metavar="VALUE",
                        help="Concrete theta values; default: symbolic theta")
    parser.add_argument("--runs", type=int, default=1, help="Measured runs per case (default: 1)")
    parser.add_argument("--warmups", type=int, default=0, help="Unmeasured runs per case (default: 0)")
    parser.add_argument("--solver-timeout-ms", type=int, default=1000)
    parser.add_argument("--timeout", type=float, default=60,
                        help="Wall-time limit per analyzer process in seconds (default: 60)")
    parser.add_argument("--csv", type=Path, metavar="PATH", default=RESULTS / "rq1.csv",
                        help="Summary CSV path (default: results/rq1.csv next to this script)")
    parser.add_argument("--boundaries", nargs="?", const="retained",
                        choices=("retained", "all"),
                        help="Print retained boundary records, or use '--boundaries all' to include dropped records")
    args = parser.parse_args()
    if args.runs < 1 or args.warmups < 0 or args.solver_timeout_ms < 1 or args.timeout <= 0:
        parser.error("Runs and timeouts must be positive; warmups must be nonnegative")
    for theta in args.theta or []:
        try:
            Fraction(theta)
        except (ValueError, ZeroDivisionError):
            parser.error("Theta values must be finite decimal numbers")
        # The analyzer accepts numeric literals, rather than fraction syntax.
        if "/" in theta:
            parser.error("Use decimal theta values, such as 0.6")
    order = {name: index for index, name in enumerate(PROGRAM_ORDER)}
    programs = sorted(SUITE.glob("*.ppl"),
                      key=lambda path: (order.get(path.stem, len(order)), path.name))
    if not programs:
        parser.error("No .ppl programs found alongside this script")
    try:
        subprocess.run(["dune", "build", "bin/main.exe"], cwd=ROOT, check=True)
    except (OSError, subprocess.CalledProcessError) as error:
        print("Build failed: " + str(error), file=sys.stderr)
        return 1

    program_width = max(12, max(len(program.name) for program in programs))
    print("Counts are boundary records. Time is median analyzer process wall time, excluding build.")
    print(f"Measured runs: {args.runs}; warmups: {args.warmups}; solver timeout: {args.solver_timeout_ms} ms")
    if args.boundaries:
        print("Boundary equations use symbolic samples s1, s2, ... and exact rational constants.")
        print("Assigned surface regions also satisfy the admissible sample-domain constraints.")
    print(f"{'Program':<{program_width}} {'theta':<10} {'Extracted':>9} {'Retained':>8} "
          f"{'SAT':>5} {'UNSAT':>6} {'REDUNDANT':>9} {'UNKNOWN':>7} {'Time(s)':>9}")
    rows, failed = [], False
    for program in programs:
        for theta in args.theta or [None]:
            label = theta if theta is not None else "symbolic"
            row = {"program": program.name, "theta": label, "runs": args.runs,
                   "warmups": args.warmups, "solver_timeout_ms": args.solver_timeout_ms,
                   "timeout_s": args.timeout}
            try:
                metrics, candidates = analyze(program, theta, args)
                row.update(metrics, status="ok", error="")
                print(f"{program.name:<{program_width}} {label:<10} {row['extracted']:>9} {row['retained']:>8} "
                      f"{row['sat']:>5} {row['unsat']:>6} {row['redundant']:>9} "
                      f"{row['unknown']:>7} {row['time_s']:>9.3f}", flush=True)
                if args.boundaries:
                    print_boundaries(candidates, args.boundaries)
            except (OSError, subprocess.TimeoutExpired, ValueError, KeyError, TypeError) as error:
                failed = True
                row.update(status="error", error=str(error))
                print(f"{program.name:<{program_width}} {label:<10} ERROR", flush=True)
                print(f"{program.name} (theta={label}): {error}", file=sys.stderr)
            rows.append(row)
    fields = ["program", "theta", "extracted", "retained", *STATUSES,
              "time_s", "min_s", "max_s", "runs", "warmups", "solver_timeout_ms",
              "timeout_s", "status", "error"]
    args.csv.parent.mkdir(parents=True, exist_ok=True)
    with args.csv.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    print("Saved " + str(args.csv))
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
