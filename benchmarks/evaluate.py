"""Evaluation driver for the three research questions (tex/sections/7_evaluation.tex).

  python3 benchmarks/evaluate.py --rq1      # boundary analysis: extracted vs refined candidates
  python3 benchmarks/evaluate.py --rq2      # gradient accuracy/cost: Vela vs analytic, pathwise AD, smoothing
  python3 benchmarks/evaluate.py --rq3      # parameter synthesis: Vela vs pathwise vs gradient-free (SPSA)

Flags can be combined. RQ1 also includes benchmarks/nonlinear/; RQ2 and RQ3 use top-level programs.
Results go to benchmarks/results/: rq1.txt, rq2.csv + rq2.pdf, rq3.csv + rq3.pdf.
"""
import argparse
import csv
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RESULTS = HERE / "results"
ANALYZER = ROOT / "_build" / "default" / "bin" / "main.exe"
sys.path.insert(0, str(ROOT / "gradient"))
from estimate import Estimator, Unsupported  # noqa: E402

sys.setrecursionlimit(100000)
COLORS = {"Vela": "#2a78d6", "Pathwise AD": "#eb6834", "Smoothing": "#1baf7a", "Gradient-free (SPSA)": "#1baf7a"}
MARKERS = {"Vela": "o", "Pathwise AD": "s", "Smoothing": "^", "Gradient-free (SPSA)": "^"}


# ---------------------------------------------------------------- analyzer

def programs(include_nonlinear=False):
    """Include nonlinear boundary-analysis benchmarks only when requested."""
    paths = list(HERE.glob("*.ppl"))
    if include_nonlinear:
        paths.extend((HERE / "nonlinear").rglob("*.ppl"))
    return sorted(paths, key=lambda p: p.relative_to(HERE).as_posix().lower())


_cache = {}


def analyze(path, timeout):
    """Run the analyzer once per program; returns (report or None, seconds, error)."""
    if path not in _cache:
        start = time.perf_counter()
        try:
            out = subprocess.run([str(ANALYZER), "--json", str(path)], capture_output=True,
                                 text=True, timeout=timeout)
            seconds = time.perf_counter() - start
            if out.returncode:
                _cache[path] = (None, seconds, "analyzer error: " + out.stderr.strip())
            else:
                _cache[path] = (json.loads(out.stdout), seconds, None)
        except subprocess.TimeoutExpired:
            _cache[path] = (None, float(timeout), f"analysis timed out after {timeout}s")
    return _cache[path]


def parameters_of(e, found=None):
    found = set() if found is None else found
    if isinstance(e, dict):
        if e.get("kind") == "parameter":
            found.add(e["name"])
        for v in e.values():
            parameters_of(v, found)
    elif isinstance(e, list):
        for v in e:
            parameters_of(v, found)
    return found


class _Full(Exception):
    pass


def show(e, limit=200):
    """Infix rendering of an analyzer JSON term, truncated (outputs can be megabytes)."""
    out, size = [], [0]

    def put(s):
        out.append(s)
        size[0] += len(s)
        if size[0] > limit:
            raise _Full

    def go(e):
        k = e["kind"]
        if k == "number":
            put(e["exact"])
        elif k == "parameter":
            put(e["name"])
        elif k == "sample":
            put(f"s{e['id']}")
        elif k == "boolean" and "value" in e:
            put(str(e["value"]).lower())
        elif k in ("arithmetic", "comparison", "boolean"):
            put("(")
            go(e["left"])
            put(f" {e['op']} ")
            go(e["right"])
            put(")")
        elif k == "not":
            put("not ")
            go(e["operand"])
        elif k == "ite":
            put("ite(")
            go(e["condition"])
            put(", ")
            go(e["then"])
            put(", ")
            go(e["else"])
            put(")")
        elif k in ("pair", "cons"):
            a, b = ("first", "second") if k == "pair" else ("head", "tail")
            put("(")
            go(e[a])
            put(", " if k == "pair" else " :: ")
            go(e[b])
            put(")")
        else:
            put(k)
    try:
        go(e)
        return "".join(out)
    except _Full:
        return "".join(out)[:limit] + " ..."


# ---------------------------------------------------------------- RQ1

def rq1(args):
    lines, rows = [], []
    for path in programs(include_nonlinear=True):
        name = path.relative_to(HERE).as_posix()
        print(f"[rq1] analyzing {name} ...", flush=True)
        report, seconds, error = analyze(path, args.timeout)
        if report is None:
            rows.append((str(Path(name).with_suffix("")), "-", "-", "-", "-", "-", f"{seconds:.2f}", error))
            lines += [f"== {name}", f"   {error}", ""]
            continue
        cands = report["candidates"]
        status = [c["solver"] for c in cands]
        rows.append((str(Path(name).with_suffix("")), len(report["samples"]), len(cands), report["retained_count"],
                     status.count("sat"), status.count("unsat"), f"{seconds:.2f}",
                     f"{status.count('unknown')} unknown" if "unknown" in status else ""))
        lines.append(f"== {name}  ({seconds:.2f}s, {len(report['samples'])} base samples, "
                     f"parameters: {', '.join(sorted(parameters_of(report['value']))) or 'none'})")
        lines.append(f"   Extracted candidates B: {len(cands)}")
        for i, c in enumerate(cands, 1):
            verdict = {"sat": "retained", "unsat": "DROPPED", "unknown": "retained (unknown)"}[c["solver"]]
            lines.append(f"   {i:3d}. [{c['solver']:7s} -> {verdict}] guard: {show(c['guard'])}")
            lines.append(f"        path: {show(c['path'])}")
            lines.append(f"        local sides: {show(c['local_minus'], 90)} | {show(c['local_plus'], 90)}")
            if "reason" in c:
                lines.append(f"        reason: {c['reason']}")
        lines.append(f"   Refined candidates B*: {report['retained_count']}")
        for i, c in enumerate((c for c in cands if c["retained"]), 1):
            lines.append(f"   {i:3d}. {show(c['guard'])} = 0  [{c['solver']}]")
        lines.append("")
    header = ("program", "samples", "|B|", "|B*|", "sat", "unsat", "time(s)", "note")
    widths = [max(len(str(r[i])) for r in rows + [header]) for i in range(len(header))]
    fmt = lambda r: "  ".join(str(x).ljust(w) for x, w in zip(r, widths)).rstrip()
    table = [fmt(header), fmt(["-" * w for w in widths])] + [fmt(r) for r in rows]
    text = "\n".join(["RQ1: boundary analysis (extracted B vs refined B*)", ""] + table + ["", ""] + lines)
    print("\n" + text)
    (RESULTS / "rq1.txt").write_text(text + "\n")
    print(f"[rq1] wrote {RESULTS / 'rq1.txt'}")


# ---------------------------------------------------------------- gradient methods

def Phi(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def phi(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)


def draw(est, rng):
    """Same base-draw convention as gradient/estimate.py."""
    return {i: Q(rng.random() if d == "uniform" else rng.gauss(0, 1)) for i, d in est.samples.items()}


def vela(est, n, seed):
    r = est.estimate(n, seed)
    return [r["gradient"][k]["mean"] for k in est.names], n * (1 + 2 * r["surfaces"])


def pathwise(est, n, seed):
    """Branchwise derivative only (what naive AD computes): Vela's interior term alone."""
    rng, acc = random.Random(seed), [0.0] * len(est.names)
    for _ in range(n):
        g = est.evaluate(est.value, draw(est, rng))[1]
        acc = [a + b for a, b in zip(acc, g)]
    return [a / n for a in acc], n


def smoothing(est, n, seed, eta):
    """Khajwal, Ong & Wagner: replace each guard a < b by sigmoid((b - a)/eta), then pathwise AD."""
    rng, acc, names = random.Random(seed), [0.0] * len(est.names), est.names
    consts = {}

    def num(e):
        if id(e) not in consts:
            consts[id(e)] = float(Q(e["exact"].strip("()")))
        return consts[id(e)]

    def value(e, s):
        k = e["kind"]
        if k == "number":
            return num(e), [0.0] * len(names)
        if k == "sample":
            return s[e["id"]], [0.0] * len(names)
        if k == "parameter":
            return float(est.parameters[e["name"]]), [float(x == e["name"]) for x in names]
        if k == "ite":
            p, dp = truth(e["condition"], s)
            t, dt = value(e["then"], s)
            f, df = value(e["else"], s)
            return p * t + (1 - p) * f, [a * (t - f) + p * b + (1 - p) * c for a, b, c in zip(dp, dt, df)]
        x, dx = value(e["left"], s)
        y, dy = value(e["right"], s)
        op = e["op"]
        if op == "+":
            return x + y, [a + b for a, b in zip(dx, dy)]
        if op == "-":
            return x - y, [a - b for a, b in zip(dx, dy)]
        if op == "*":
            return x * y, [a * y + x * b for a, b in zip(dx, dy)]
        return x / y, [(a * y - x * b) / (y * y) for a, b in zip(dx, dy)]

    def truth(e, s):
        k = e["kind"]
        if k == "boolean" and "value" in e:
            return float(e["value"]), [0.0] * len(names)
        if k == "not":
            p, dp = truth(e["operand"], s)
            return 1 - p, [-a for a in dp]
        if k == "boolean":
            p, dp = truth(e["left"], s)
            q, dq = truth(e["right"], s)
            if e["op"] == "and":
                return p * q, [a * q + p * b for a, b in zip(dp, dq)]
            return p + q - p * q, [a + b - a * q - p * b for a, b in zip(dp, dq)]
        x, dx = value(e["left"], s)
        y, dy = value(e["right"], s)
        z = max(-60.0, min(60.0, (y - x) / eta))
        p = 1 / (1 + math.exp(-z))
        return p, [p * (1 - p) * (b - a) / eta for a, b in zip(dx, dy)]

    for _ in range(n):
        s = {i: float(x) for i, x in draw(est, rng).items()}
        acc = [a + b for a, b in zip(acc, value(est.value, s)[1])]
    return [a / n for a in acc], n


def gradient_free(report, theta, n, seed, c=0.1):
    """Two-sided SPSA with common random numbers, using only program outputs."""
    rng = random.Random(seed)
    delta = {k: rng.choice((-1.0, 1.0)) for k in theta}
    ests = [Estimator(report, {k: str(v + sign * c * delta[k]) for k, v in theta.items()}) for sign in (1, -1)]
    total = [0.0, 0.0]
    for _ in range(n):
        s = draw(ests[0], rng)
        for j, est in enumerate(ests):
            total[j] += est.evaluate(est.value, s)[0]
    diff = (total[0] - total[1]) / n
    return [diff / (2 * c * delta[k]) for k in sorted(theta)], 2 * n


# ---------------------------------------------------------------- RQ2

def bnn_analytic(p):
    x = p["_x"]
    s = 0.2 * math.sqrt(x * x + 1)
    ds = 0.2 * x / math.sqrt(x * x + 1)
    g = {"_mub3": 1.0, "_x": 0.0}
    for h, (w, b, out) in enumerate((("_muw1", "_mub1", "_muw3"), ("_muw2", "_mub2", "_muw4"))):
        m = x * p[w] + p[b]
        k = m / s
        g[w] = p[out] * Phi(k) * x
        g[b] = p[out] * Phi(k)
        g[out] = m * Phi(k) + s * phi(k)
        g["_x"] += p[out] * (Phi(k) * p[w] + phi(k) * ds)
    return g


# Evaluation points and closed-form gradients of E[output]; None = no closed form.
RQ2 = {
    "esop": ([{"theta": t} for t in (-1, -0.5, 0, 0.5, 1)],
             lambda p: {"theta": -p["theta"] + phi(p["theta"])}),
    "gauss_branching": ([{"mu1": 0.0, "mu2": 1.0}, {"mu1": 2.0, "mu2": -1.0}],
                        lambda p: {"mu1": phi(p["mu1"] / 5) / 5 * (p["mu2"] + 2), "mu2": Phi(p["mu1"] / 5)}),
    "Optim6": ([{"_coeff": c} for c in (-1, 0, 1)],
               lambda p: {"_coeff": -10 * phi(p["_coeff"])}),
    "stress": ([{"theta": t} for t in (-1, 0, 1)],
               lambda p: {"theta": phi(p["theta"] / math.sqrt(2)) / math.sqrt(2)}),
    "bnn_one_x": ([{"_x": 1.0, "_muw1": 0.5, "_muw2": -0.3, "_muw3": 1.0, "_muw4": 0.8,
                    "_mub1": 0.1, "_mub2": 0.2, "_mub3": 0.0}], bnn_analytic),
    "thermostat": ([{"_tOn": 18.0, "_tOff": 21.0}], None),
}


def rq2(args):
    rows, errors = [], {}
    methods = {"Vela": vela, "Pathwise AD": pathwise,
               "Smoothing": lambda est, n, seed: smoothing(est, n, seed, args.eta)}
    for path in programs():
        if path.stem not in RQ2:
            continue
        points, analytic = RQ2[path.stem]
        print(f"[rq2] {path.name}", flush=True)
        report, _, error = analyze(path, args.timeout)
        if report is not None:
            try:
                Estimator(report, {k: str(v) for k, v in points[0].items()})
            except Unsupported as e:
                error = f"unsupported by Vela estimator: {e}"
        if analytic is None and error is None:
            error = "no analytic reference gradient"
        if error:
            print(f"   skipped: {error}")
            rows.append(dict(program=path.stem, status=error))
            continue
        for point in points:
            est = Estimator(report, {k: str(v) for k, v in point.items()})
            truth = analytic(point)
            norm = math.sqrt(sum(truth[k] ** 2 for k in est.names))
            label = ", ".join(f"{k}={v:g}" for k, v in sorted(point.items()))
            for method, run in methods.items():
                for n in args.budgets:
                    sq, secs = [], []
                    for rep in range(args.reps):
                        start = time.perf_counter()
                        grad, evals = run(est, n, 1000 * rep + n)
                        seconds = time.perf_counter() - start
                        sq.append(sum((g - truth[k]) ** 2 for g, k in zip(grad, est.names)))
                        secs.append(seconds)
                        for g, k in zip(grad, est.names):
                            rows.append(dict(program=path.stem, point=label, method=method, draws=n, rep=rep,
                                             evaluations=evals, seconds=f"{seconds:.6f}", parameter=k,
                                             estimate=f"{g:.8g}", analytic=f"{truth[k]:.8g}", status="ok"))
                    rel = math.sqrt(sum(sq) / len(sq)) / norm
                    errors.setdefault((path.stem, method, n), []).append((rel, sum(secs) / len(secs)))
                    print(f"   {label:30.30s} {method:12s} N={n:<6d} rel.RMSE={rel:9.4f}  "
                          f"{sum(secs) / len(secs):8.4f}s/estimate", flush=True)
    fields = ["program", "point", "method", "draws", "rep", "evaluations", "seconds", "parameter",
              "estimate", "analytic", "status"]
    with (RESULTS / "rq2.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fields)
        w.writeheader()
        w.writerows(rows)
    plot_rq2(errors, args)
    print(f"[rq2] wrote {RESULTS / 'rq2.csv'} and {RESULTS / 'rq2.pdf'}")


def style(ax):
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    ax.grid(True, which="major", color="#e4e3dd", linewidth=0.6)
    ax.set_axisbelow(True)


def plot_rq2(errors, args):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    progs = sorted({p for p, _, _ in errors}, key=str.lower)
    methods = list(dict.fromkeys(m for _, m, _ in errors))
    fig, axes = plt.subplots(2, len(progs), figsize=(3.0 * len(progs), 5.6), squeeze=False)
    for j, prog in enumerate(progs):
        for m in methods:
            pts = [(n, errors[(prog, m, n)]) for n in args.budgets if (prog, m, n) in errors]
            # Mean over evaluation points; floor so exact (zero-error) estimates stay on the log axis.
            err = [max(1e-16, sum(r for r, _ in v) / len(v)) for _, v in pts]
            sec = [sum(t for _, t in v) / len(v) for _, v in pts]
            kw = dict(color=COLORS[m], marker=MARKERS[m], markersize=5, linewidth=2, label=m)
            axes[0][j].plot([n for n, _ in pts], err, **kw)
            axes[1][j].plot(sec, err, **kw)
        axes[0][j].set_title(prog, fontsize=10)
        axes[0][j].set_xlabel("sample budget N")
        axes[1][j].set_xlabel("runtime per estimate (s)")
        for ax in (axes[0][j], axes[1][j]):
            ax.set_xscale("log")
            ax.set_yscale("log")
            style(ax)
    axes[0][0].set_ylabel("relative RMSE vs analytic")
    axes[1][0].set_ylabel("relative RMSE vs analytic")
    handles, labels = axes[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=len(labels), frameon=False)
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig(RESULTS / "rq2.pdf")
    plt.close(fig)


# ---------------------------------------------------------------- RQ3

# Objective = the program's own return value. `exact` gives the true objective for
# reporting (None -> plain Monte Carlo with a fixed seed).
RQ3 = {
    "stress": dict(sense="max", init={"theta": -2.0}, bounds={"theta": (-3.0, 3.0)},
                   ylabel="P(strength > stress)", exact=lambda p: Phi(p["theta"] / math.sqrt(2))),
    "Optim6": dict(sense="max", init={"_coeff": 2.0}, bounds={"_coeff": (-3.0, 3.0)},
                   ylabel="E[a]", exact=lambda p: 5 - 10 * Phi(p["_coeff"])),
    "thermostat": dict(sense="max", init={"_tOn": 18.0, "_tOff": 21.0},
                       bounds={"_tOn": (15.0, 25.0), "_tOff": (15.0, 25.0)},
                       threshold_gap=0.1,
                       ylabel="E[negative mean squared error]", exact=None),
}


def objective(report, spec, theta, draws=20000):
    if spec["exact"]:
        return spec["exact"](theta)
    est = Estimator(report, {k: str(v) for k, v in theta.items()})
    rng = random.Random(12345)
    return sum(float(est.evaluate(est.value, draw(est, rng))[0]) for _ in range(draws)) / draws


def optimize(report, spec, method, lr, seed, args):
    """Projected SGD; identical optimizer, init, step budget and lr grid for every method."""
    theta = dict(spec["init"])
    sign = 1 if spec["sense"] == "max" else -1
    evals, seconds = 0, 0.0
    trace = [(0, evals, seconds, dict(theta), objective(report, spec, theta))]
    for step in range(1, args.steps + 1):
        start = time.perf_counter()
        s = seed * 100003 + step
        if method == "Gradient-free (SPSA)":
            grad, used = gradient_free(report, theta, args.draws_per_step, s)
        else:
            est = Estimator(report, {k: str(v) for k, v in theta.items()})
            grad, used = (vela if method == "Vela" else pathwise)(est, args.draws_per_step, s)
        for k, g in zip(sorted(theta), grad):
            lo, hi = spec["bounds"][k]
            theta[k] = min(hi, max(lo, theta[k] + sign * lr * g))
        if "threshold_gap" in spec:
            gap = spec["threshold_gap"]
            if theta["_tOff"] - theta["_tOn"] < gap:
                lo = max(spec["bounds"]["_tOn"][0], spec["bounds"]["_tOff"][0] - gap)
                hi = min(spec["bounds"]["_tOn"][1], spec["bounds"]["_tOff"][1] - gap)
                on = min(hi, max(lo, (theta["_tOn"] + theta["_tOff"] - gap) / 2))
                theta.update(_tOn=on, _tOff=on + gap)
        seconds += time.perf_counter() - start
        evals += used
        trace.append((step, evals, seconds, dict(theta), objective(report, spec, theta)))
    return trace


def rq3(args):
    rows, best = [], {}
    methods = ["Vela", "Pathwise AD", "Gradient-free (SPSA)"]
    for path in programs():
        if path.stem not in RQ3:
            continue
        spec = RQ3[path.stem]
        print(f"[rq3] {path.name}", flush=True)
        report, _, error = analyze(path, args.timeout)
        if report is not None:
            try:
                Estimator(report, {k: str(v) for k, v in spec["init"].items()})
            except Unsupported as e:
                error = f"unsupported by Vela estimator: {e}"
        if error:
            print(f"   skipped: {error}")
            rows.append(dict(program=path.stem, status=error))
            continue
        for method in methods:
            finals = {}
            for lr in args.lrs:
                traces = [optimize(report, spec, method, lr, seed, args) for seed in range(args.seeds)]
                finals[lr] = sum(t[-1][4] for t in traces) / len(traces)
                for seed, trace in enumerate(traces):
                    for step, evals, seconds, theta, obj in trace:
                        rows.append(dict(program=path.stem, method=method, lr=lr, seed=seed, step=step,
                                         evaluations=evals, seconds=f"{seconds:.6f}",
                                         theta=" ".join(f"{k}={v:.6g}" for k, v in sorted(theta.items())),
                                         objective=f"{obj:.8g}", status="ok"))
            pick = (max if spec["sense"] == "max" else min)(finals, key=finals.get)
            best[(path.stem, method)] = pick
            print(f"   {method:22s} final objective by lr: "
                  + ", ".join(f"{lr:g}:{v:.4f}" for lr, v in finals.items()) + f"  -> lr={pick:g}", flush=True)
    for r in rows:
        r["selected_lr"] = r.get("status") == "ok" and best.get((r["program"], r["method"])) == r["lr"]
    fields = ["program", "method", "lr", "selected_lr", "seed", "step", "evaluations", "seconds", "theta",
              "objective", "status"]
    with (RESULTS / "rq3.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fields)
        w.writeheader()
        w.writerows(rows)
    plot_rq3([r for r in rows if r.get("selected_lr")], methods)
    print(f"[rq3] wrote {RESULTS / 'rq3.csv'} and {RESULTS / 'rq3.pdf'}")


def plot_rq3(rows, methods):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    progs = list(dict.fromkeys(r["program"] for r in rows))
    if not progs:
        return
    fig, axes = plt.subplots(1, len(progs), figsize=(3.6 * len(progs), 3.2), squeeze=False)
    for ax, prog in zip(axes[0], progs):
        for m in methods:
            sel = [r for r in rows if r["program"] == prog and r["method"] == m]
            steps = sorted({r["step"] for r in sel})
            x, mean, lo, hi = [], [], [], []
            for s in steps:
                at = [r for r in sel if r["step"] == s]
                vals = [float(r["objective"]) for r in at]
                mu = sum(vals) / len(vals)
                sd = math.sqrt(sum((v - mu) ** 2 for v in vals) / max(1, len(vals) - 1))
                x.append(max(1, sum(r["evaluations"] for r in at) / len(at)))
                mean.append(mu)
                lo.append(mu - sd)
                hi.append(mu + sd)
            ax.plot(x, mean, color=COLORS[m], linewidth=2, label=f"{m} (lr={sel[0]['lr']:g})",
                    marker=MARKERS[m], markevery=max(1, len(x) // 6), markersize=5)
            ax.fill_between(x, lo, hi, color=COLORS[m], alpha=0.15, linewidth=0)
        ax.set_xscale("log")
        ax.set_title(prog, fontsize=10)
        ax.set_xlabel("cumulative program evaluations")
        ax.set_ylabel(RQ3[prog]["ylabel"])
        style(ax)
        ax.legend(frameon=False, fontsize=7)
    fig.tight_layout()
    fig.savefig(RESULTS / "rq3.pdf")
    plt.close(fig)


# ---------------------------------------------------------------- main

def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--rq1", action="store_true", help="boundary analysis")
    p.add_argument("--rq2", action="store_true", help="gradient estimation")
    p.add_argument("--rq3", action="store_true", help="parameter synthesis")
    p.add_argument("--timeout", type=float, default=300, help="analyzer timeout per program, seconds")
    p.add_argument("--budgets", type=int, nargs="+", default=[10, 100, 1000, 10000], help="RQ2 sample budgets")
    p.add_argument("--reps", type=int, default=10, help="RQ2 independent repetitions per budget")
    p.add_argument("--eta", type=float, default=0.1, help="RQ2 smoothing temperature")
    p.add_argument("--steps", type=int, default=40, help="RQ3 optimizer steps")
    p.add_argument("--draws-per-step", type=int, default=64, help="RQ3 Monte Carlo draws per step")
    p.add_argument("--seeds", type=int, default=5, help="RQ3 random restarts per configuration")
    p.add_argument("--lrs", type=float, nargs="+", default=[0.01, 0.03, 0.1, 0.3, 1.0],
                   help="RQ3 learning-rate grid (same tuning budget for every method)")
    args = p.parse_args()
    if not (args.rq1 or args.rq2 or args.rq3):
        p.error("choose at least one of --rq1, --rq2, --rq3")
    RESULTS.mkdir(exist_ok=True)
    subprocess.run(["dune", "build"], cwd=ROOT, check=True)
    if args.rq1:
        rq1(args)
    if args.rq2:
        rq2(args)
    if args.rq3:
        rq3(args)


if __name__ == "__main__":
    main()
