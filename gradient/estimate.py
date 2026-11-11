"""Expectation gradients from diff_ppl JSON; Monte Carlo or exact integration."""
import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import random
import statistics
import subprocess


class Unsupported(ValueError):
    pass


def number(node):
    return Q(node["exact"].strip("()"))


def combine(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + sign * c
    return {m: c for m, c in out.items() if c}


def polynomial(e):
    """Exact polynomial normal form, used only to certify/identify guards."""
    k = e["kind"]
    if k == "number":
        return {(): number(e)} if number(e) else {}
    if k in ("sample", "parameter"):
        name = "s:" + str(e["id"]) if k == "sample" else "p:" + e["name"]
        return {(name,): Q(1)}
    if k != "arithmetic":
        raise Unsupported("Guards must be polynomial and affine in base samples")
    a, b = polynomial(e["left"]), polynomial(e["right"])
    op = e["op"]
    if op in ("+", "-"):
        return combine(a, b, 1 if op == "+" else -1)
    if op == "/":
        if set(b) != {()}:
            raise Unsupported("Division requires a nonzero numeric constant denominator")
        return {m: c / b[()] for m, c in a.items()}
    if op != "*":
        raise Unsupported("Unknown arithmetic operation")
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def canonical(poly):
    items = sorted((m, c) for m, c in poly.items() if c)
    scale = items[0][1] if items else Q(1)
    return tuple((m, c / scale) for m, c in items)


def poly_value(poly, env, derivative=None):
    total = Q(0)
    for monomial, coefficient in poly.items():
        factors = list(monomial)
        if derivative is not None:
            count = factors.count(derivative)
            if not count:
                continue
            coefficient *= count
            factors.remove(derivative)
        for name in factors:
            coefficient *= env[name]
        total += coefficient
    return total


class Estimator:
    def __init__(self, report, parameters):
        # Schema 5 adds refined traces; the original value/samples remain compatible.
        if report.get("schema_version") not in (3, 5):
            raise Unsupported("Expected analyzer JSON schema_version 3 or 5")
        if any(b["retained"] and b["solver"] != "sat" for b in report["candidates"]):
            raise Unsupported("Retained solver-unknown boundaries are unsupported")
        self.value = report["value"]
        self.parameters = {name: Q(str(value)) for name, value in parameters.items()}
        self.names = sorted(self.parameters)
        self.samples = {s["id"]: s["distribution"] for s in report["samples"]}
        if len(self.samples) != len(report["samples"]):
            raise Unsupported("Duplicate sample IDs")
        if any(d not in ("uniform", "gaussian") for d in self.samples.values()):
            raise Unsupported("Only independent Uniform(0,1) and Gaussian(0,1) bases are supported")
        self.guards = {}
        self.comparisons = {}
        self.validate(self.value, numeric=True)
        self.env = {"p:" + n: v for n, v in self.parameters.items()}
        self.boundaries = []
        seen = set()
        for poly in self.guards.values():
            # Evaluate parameter coefficients exactly at the requested point.
            c = poly_value(poly, {**self.env, **{"s:" + str(i): Q(0) for i in self.samples}})
            a = {}
            for i in self.samples:
                unit = {"s:" + str(k): Q(int(k == i)) for k in self.samples}
                a[i] = poly_value(poly, {**self.env, **unit}) - c
            if not any(a.values()):
                raise Unsupported("A guard has zero sample normal at the requested parameters")
            key = canonical({(): c, **{("s:" + str(i),): x for i, x in a.items() if x}})
            if key in seen:
                raise Unsupported("Distinct parameterized surfaces coincide at this parameter point")
            seen.add(key)
            j = max(a, key=lambda i: abs(a[i]))
            if self.samples[j] == "uniform" and sum(x != 0 for x in a.values()) == 1:
                if -c / a[j] in (0, 1):
                    raise Unsupported("A surface coincides with a Uniform support face")
            self.boundaries.append((poly, c, a, j))

    def validate(self, e, numeric):
        k = e["kind"]
        if numeric:
            if k == "number":
                number(e)
            elif k == "parameter":
                if e["name"] not in self.parameters:
                    raise Unsupported("Missing parameter: " + e["name"])
            elif k == "sample":
                if e["id"] not in self.samples:
                    raise Unsupported("Unknown base sample")
            elif k == "arithmetic":
                if e["op"] not in ("+", "-", "*", "/"):
                    raise Unsupported("Unknown arithmetic operation")
                if e["op"] == "/" and (e["right"]["kind"] != "number" or not number(e["right"])):
                    raise Unsupported("Division requires a nonzero numeric constant denominator")
                self.validate(e["left"], True)
                self.validate(e["right"], True)
            elif k == "ite":
                self.validate(e["condition"], False)
                self.validate(e["then"], True)
                self.validate(e["else"], True)
            else:
                raise Unsupported("Expected a scalar piecewise-polynomial output; got " + k)
        elif k == "boolean" and "value" in e:
            return
        elif k == "comparison" and e["op"] in ("<", "<="):
            self.validate(e["left"], True)
            self.validate(e["right"], True)
            poly = combine(polynomial(e["left"]), polynomial(e["right"]), -1)
            if any(sum(v.startswith("s:") for v in m) > 1 for m in poly):
                raise Unsupported("Non-affine boundary in base-sample space")
            if not any(any(v.startswith("s:") for v in m) for m in poly):
                raise Unsupported("Parameter-only or identically constant comparisons are unsupported")
            self.guards.setdefault(canonical(poly), poly)
            self.comparisons[id(e)] = poly
        elif k == "boolean" and e.get("op") in ("and", "or"):
            self.validate(e["left"], False)
            self.validate(e["right"], False)
        elif k == "not":
            self.validate(e["operand"], False)
        else:
            raise Unsupported("Unsupported Boolean expression: " + k)

    def evaluate(self, e, s, trace=None):
        """Forward AD; on a surface, exact directional signs choose limiting branches."""
        k = e["kind"]
        zero = [0.0] * len(self.names)
        if k == "number":
            return float(number(e)), zero
        if k == "sample":
            return float(s[e["id"]]), zero
        if k == "parameter":
            return float(self.parameters[e["name"]]), [float(n == e["name"]) for n in self.names]
        if k == "ite":
            return self.evaluate(e["then"] if self.condition(e["condition"], s, trace) else e["else"], s, trace)
        x, dx = self.evaluate(e["left"], s, trace)
        y, dy = self.evaluate(e["right"], s, trace)
        op = e["op"]
        if op == "+":
            return x + y, [a + b for a, b in zip(dx, dy)]
        if op == "-":
            return x - y, [a - b for a, b in zip(dx, dy)]
        if op == "*":
            return x * y, [a * y + x * b for a, b in zip(dx, dy)]
        return x / y, [a / y for a in dx]  # denominator certified constant

    def condition(self, e, s, trace):
        k = e["kind"]
        if k == "boolean":
            if "value" in e:
                return e["value"]
            a = self.condition(e["left"], s, trace)
            return (a and self.condition(e["right"], s, trace)) if e["op"] == "and" else (a or self.condition(e["right"], s, trace))
        if k == "not":
            return not self.condition(e["operand"], s, trace)
        poly = self.comparisons[id(e)]
        env = {**self.env, **{"s:" + str(i): Q(x) for i, x in s.items()}}
        value = poly_value(poly, env)
        if value == 0:
            if trace is None:
                raise Unsupported("An interior draw lies exactly on a boundary; change the seed")
            j, direction = trace
            value = direction * poly_value(poly, env, "s:" + str(j))
            if value == 0:
                raise Unsupported("Boundary sample lies on another surface; change the seed")
        return value < 0

    def estimate(self, draws=1000, seed=0, backend="mc"):
        if backend not in ("mc", "exact", "auto"):
            raise ValueError("Unknown backend: " + backend)
        fallback_reason = None
        if backend != "mc":
            if __package__:
                from .exact import integrate_exact
            else:
                from exact import integrate_exact
            try:
                return integrate_exact(self, Unsupported, number, poly_value)
            except Unsupported as error:
                if backend == "exact":
                    raise
                fallback_reason = str(error)
        if draws < 2:
            raise ValueError("At least two draws are required for standard errors")
        rng = random.Random(seed)
        interior, boundary, total = [], [], []
        for _ in range(draws):
            def sample():
                return {i: Q(rng.random() if d == "uniform" else rng.gauss(0, 1)) for i, d in self.samples.items()}
            smooth = self.evaluate(self.value, sample())[1]
            correction = [0.0] * len(self.names)
            # Sum all unique surfaces (Lee et al.'s no-subsampling variant).
            for poly, c, a, j in self.boundaries:
                s = sample()
                s[j] = -(c + sum(a[i] * s[i] for i in s if i != j)) / a[j]
                if self.samples[j] == "uniform":
                    if not 0 < s[j] < 1:
                        continue
                    density = 1.0
                else:
                    x = float(s[j])
                    density = math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)
                direction = 1 if a[j] > 0 else -1
                plus = self.evaluate(self.value, s, (j, direction))[0]
                minus = self.evaluate(self.value, s, (j, -direction))[0]
                env = {**self.env, **{"s:" + str(i): x for i, x in s.items()}}
                for k, name in enumerate(self.names):
                    velocity = float(poly_value(poly, env, "p:" + name) / abs(a[j]))
                    correction[k] += density * (plus - minus) * velocity
            combined = [a + b for a, b in zip(smooth, correction)]
            if not all(math.isfinite(x) for x in smooth + correction + combined):
                raise ArithmeticError("Non-finite estimator value")
            interior.append(smooth)
            boundary.append(correction)
            total.append(combined)

        def summary(rows):
            return {name: {"mean": statistics.fmean(row[k] for row in rows),
                           "standard_error": statistics.stdev(row[k] for row in rows) / math.sqrt(draws)}
                    for k, name in enumerate(self.names)}
        return {"backend": "mc", "fallback_reason": fallback_reason,
                "draws": draws, "seed": seed, "surfaces": len(self.boundaries),
                "gradient": summary(total), "interior": summary(interior), "boundary": summary(boundary)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="Program (.ppl) or unsubstituted analyzer JSON report")
    parser.add_argument("--at", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--draws", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--backend", choices=("mc", "exact", "auto"), default="mc",
                        help="Integration backend (default: mc); auto tries exact then falls back to mc")
    args = parser.parse_args()
    try:
        parameters = dict(item.split("=", 1) for item in args.at)
        source = Path(args.source).resolve()
        if source.suffix == ".ppl":
            result = subprocess.run(
                ["dune", "exec", "diff_ppl", "--", "--json", str(source)],
                cwd=Path(__file__).resolve().parents[1],
                capture_output=True, text=True, check=True)
            report = json.loads(result.stdout)
        else:
            with source.open() as stream:
                report = json.load(stream)
        estimator = Estimator(report, parameters)
        result = estimator.estimate(args.draws, args.seed, args.backend)
        if result["backend"] == "exact":
            print(f"Expectation gradient (exact backend, {result['surfaces']} boundary surfaces)")
        else:
            print(f"Expectation gradient ({result['draws']} draws, {result['surfaces']} boundary surfaces, seed {result['seed']})")
            if result["fallback_reason"]:
                print("Backend: mc (auto fallback: " + result["fallback_reason"] + ")")
        if not estimator.names:
            print("No parameters to differentiate.")
        for name in estimator.names:
            print(f"\n{name} = {float(estimator.parameters[name]):.6g}")
            for key, label in (("gradient", "Gradient"), ("interior", "Interior"), ("boundary", "Boundary")):
                estimate = result[key][name]
                if result["backend"] == "exact":
                    print(f"  {label:8s} {estimate['exact']}  (approximately {estimate['mean']:.6g})")
                else:
                    print(f"  {label:8s} {estimate['mean']:.6g}  (standard error {estimate['standard_error']:.3g})")
    except subprocess.CalledProcessError as error:
        parser.exit(2, f"gradient: analyzer failed\n{error.stderr}")
    except (ValueError, ArithmeticError, KeyError, OSError) as error:
        parser.exit(2, f"gradient: {error}\n")


if __name__ == "__main__":
    main()
