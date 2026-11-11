"""Exact backend checks against independently derived expectations."""
import subprocess
import unittest

import sympy as sp

from gradient.estimate import Estimator, Unsupported
from gradient.test_estimate import ROOT, analyze, setUpModule


class ExactTests(unittest.TestCase):
    def check(self, source, parameters, expected, interior=None, boundary=None):
        result = Estimator(analyze(source), parameters).estimate(backend="exact")
        self.assertEqual(result["backend"], "exact")
        for part, targets in (("gradient", expected), ("interior", interior), ("boundary", boundary)):
            for name, target in (targets or {}).items():
                self.assertEqual(sp.simplify(sp.sympify(result[part][name]["exact"]) - target), 0)
                self.assertNotIn("standard_error", result[part][name])
        return result

    def test_moments(self):
        self.check("let u = uniform(0,1) in let z = gaussian(0,1) in theta*u*u + theta*theta*z*z",
                   {"theta": "2/5"}, {"theta": sp.Rational(17, 15)})
        self.check("let x = gaussian(theta,1) in x*x", {"theta": ".7"}, {"theta": sp.Rational(7, 5)})
        self.check("theta*theta", {"theta": "2"}, {"theta": 4})
        self.check("let z = gaussian(0,1) in theta*z*z*z*z", {"theta": "1"}, {"theta": 3})

    def test_uniform_pieces(self):
        self.check("let u = uniform(0,1) in if u < theta then theta else 0", {"theta": ".4"},
                   {"theta": sp.Rational(4, 5)}, {"theta": sp.Rational(2, 5)}, {"theta": sp.Rational(2, 5)})
        self.check("let u = uniform(0,1) in if u < theta then theta-u else 0", {"theta": ".4"},
                   {"theta": sp.Rational(2, 5)}, boundary={"theta": 0})
        self.check("let u = uniform(0,1) in if theta <= u then 0 else 2", {"theta": ".4"}, {"theta": 2})
        self.check("let u = uniform(0,1) in if u < theta then theta else 0", {"theta": "2"}, {"theta": 1})
        self.check("let u = uniform(0,1) in if u < theta then (if u < 0.2 then theta*u else theta*u*u) else 0",
                   {"theta": ".4"}, {"theta": sp.Rational(77, 750)})

    def test_gaussian_pieces(self):
        phi = sp.exp(-sp.Rational(1, 8)) / sp.sqrt(2*sp.pi)
        self.check("let z = gaussian(0,1) in if z < theta then 1 else 0", {"theta": ".5"}, {"theta": phi})
        self.check("let z = gaussian(0,1) in if z < theta then theta-z else 0", {"theta": ".5"},
                   {"theta": (1 + sp.erf(sp.sqrt(2)/4))/2}, boundary={"theta": 0})
        self.check("let z = gaussian(0,1) in if z < 0 then theta*z*z else theta*z*z*z*z",
                   {"theta": "1"}, {"theta": 2})
        self.check("let x = gaussian(mu,2) in if x < 0 then 1 else 0",
                   {"mu": "1"}, {"mu": -phi/2})

    def test_selection(self):
        estimator = Estimator(analyze("let u = uniform(0,1) in let v = uniform(0,1) in if u+v < theta then 1 else 0"), {"theta": ".5"})
        with self.assertRaisesRegex(Unsupported, "single base sample"):
            estimator.estimate(backend="exact")
        result = estimator.estimate(draws=10, backend="auto")
        self.assertEqual(result["backend"], "mc")
        self.assertIn("single base sample", result["fallback_reason"])
        simple = Estimator(analyze("theta*theta"), {"theta": "2"})
        self.assertEqual(simple.estimate(draws=0, backend="auto")["gradient"]["theta"]["exact"], "4")

    def test_cli(self):
        for backend in ("exact", "auto"):
            result = subprocess.run(["python3", str(ROOT / "gradient/estimate.py"),
                                     str(ROOT / "examples/symbolic/threshold.ppl"),
                                     "--at", "theta=.4", "--backend", backend],
                                    cwd="/tmp", text=True, capture_output=True, check=True)
            self.assertIn("exact backend", result.stdout)
            self.assertIn("Gradient 1", result.stdout)
            self.assertNotIn("standard error", result.stdout)


if __name__ == "__main__":
    unittest.main()
