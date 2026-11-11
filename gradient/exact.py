"""Exact moments and one-dimensional boundary integration (optional SymPy)."""


def integrate_exact(estimator, unsupported, number, poly_value):
    try:
        import sympy as sp
    except ImportError as error:
        raise unsupported("The exact backend requires SymPy: python3 -m pip install -r gradient/requirements-exact.txt") from error

    if estimator.boundaries and len(estimator.samples) != 1:
        raise unsupported("Exact branching currently requires a single base sample; use --backend mc or auto")

    parameters = {n: sp.Symbol("p:" + n, real=True) for n in estimator.names}
    samples = {i: sp.Symbol("s:" + str(i), real=True) for i in estimator.samples}
    at = {parameters[n]: sp.Rational(v) for n, v in estimator.parameters.items()}

    def expression(e, point=None, trace=None):
        k = e["kind"]
        if k == "number":
            return sp.Rational(number(e))
        if k == "parameter":
            return parameters[e["name"]]
        if k == "sample":
            return samples[e["id"]]
        if k == "ite":
            branch = "then" if estimator.condition(e["condition"], point or {}, trace) else "else"
            return expression(e[branch], point, trace)
        left = expression(e["left"], point, trace)
        right = expression(e["right"], point, trace)
        return {"+": lambda: left + right, "-": lambda: left - right,
                "*": lambda: left * right, "/": lambda: left / right}[e["op"]]()

    def density(x):
        if x in (-sp.oo, sp.oo):
            return sp.S.Zero
        return sp.exp(-x*x/2) / sp.sqrt(2*sp.pi)

    def moments(distribution, lo, hi, degree):
        if distribution == "uniform":
            return [(hi**(k+1) - lo**(k+1)) / (k+1) for k in range(degree+1)]
        values = [(sp.erf(hi/sp.sqrt(2)) - sp.erf(lo/sp.sqrt(2))) / 2]
        if degree:
            values.append(density(lo) - density(hi))
        def edge(x, power):
            return sp.S.Zero if x in (-sp.oo, sp.oo) else x**power * density(x)
        for k in range(2, degree+1):
            values.append(edge(lo, k-1) - edge(hi, k-1) + (k-1)*values[k-2])
        return values

    def integral(expr, i, lo, hi):
        poly = sp.Poly(sp.expand(expr), samples[i])
        degree = max(0, int(poly.degree())) if not poly.is_zero else 0
        values = moments(estimator.samples[i], lo, hi, degree)
        return sp.Add(*(coefficient * values[power[0]] for power, coefficient in poly.terms()))

    interior = {n: sp.S.Zero for n in parameters}
    boundary = dict(interior)
    if not estimator.boundaries:
        expr = expression(estimator.value)
        for n, parameter in parameters.items():
            value = sp.diff(expr, parameter).subs(at)
            for i, distribution in estimator.samples.items():
                lo, hi = (sp.S.Zero, sp.S.One) if distribution == "uniform" else (-sp.oo, sp.oo)
                value = integral(value, i, lo, hi)
            interior[n] = value
    else:
        i = next(iter(samples))
        uniform = estimator.samples[i] == "uniform"
        lo, hi = (sp.S.Zero, sp.S.One) if uniform else (-sp.oo, sp.oo)
        roots = sorted(-c / a[i] for _, c, a, _ in estimator.boundaries
                       if lo < -c / a[i] < hi)
        cuts = [lo, *map(sp.Rational, roots), hi]
        for left, right in zip(cuts, cuts[1:]):
            midpoint = (left + right)/2
            if left == -sp.oo:
                midpoint = right - 1 if right != sp.oo else sp.S.Zero
            elif right == sp.oo:
                midpoint = left + 1
            expr = expression(estimator.value, {i: midpoint})
            for n, parameter in parameters.items():
                interior[n] += integral(sp.diff(expr, parameter).subs(at), i, left, right)
        for poly, c, a, j in estimator.boundaries:
            root = -c / a[i]
            if not lo < root < hi:
                continue
            direction = 1 if a[i] > 0 else -1
            plus = expression(estimator.value, {i: root}, (j, direction))
            minus = expression(estimator.value, {i: root}, (j, -direction))
            jump = (plus - minus).subs(at).subs(samples[i], sp.Rational(root))
            env = {**estimator.env, "s:" + str(i): root}
            for n in parameters:
                velocity = sp.Rational(poly_value(poly, env, "p:" + n) / abs(a[i]))
                boundary[n] += jump * velocity * (1 if uniform else density(sp.Rational(root)))

    def summary(values):
        result = {}
        for name, value in values.items():
            value = sp.simplify(value)
            result[name] = {"exact": str(value), "mean": float(value)}
        return result

    return {"backend": "exact", "surfaces": len(estimator.boundaries),
            "gradient": summary({n: interior[n] + boundary[n] for n in parameters}),
            "interior": summary(interior), "boundary": summary(boundary)}
