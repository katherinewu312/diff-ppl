"""End-to-end analytic checks; run from the repository root with unittest."""
import json
import math
from pathlib import Path
import subprocess
import tempfile
import unittest

from gradient.estimate import Estimator, Unsupported


ROOT = Path(__file__).resolve().parents[1]


def setUpModule():
    subprocess.run(["dune", "build", "bin/main.exe"], cwd=ROOT, check=True)


def analyze(source):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ppl") as program:
        program.write(source)
        program.flush()
        result = subprocess.run(
            [str(ROOT / "_build/default/bin/main.exe"), "--json", program.name],
            cwd=ROOT, text=True, capture_output=True, check=True)
    return json.loads(result.stdout)


class GradientTests(unittest.TestCase):
    def test_program_command(self):
        with tempfile.TemporaryDirectory(prefix="gradient test ") as folder:
            source = Path(folder) / "threshold.ppl"
            source.write_text("let u = uniform(0,1) in if u < theta then 1 else 0")
            result = subprocess.run(
                ["python3", str(ROOT / "gradient/estimate.py"), str(source),
                 "--at", "theta=0.4", "--draws", "10"],
                cwd=folder, text=True, capture_output=True, check=True)
        self.assertIn("Expectation gradient (10 draws, 1 boundary surfaces, seed 0)", result.stdout)
        self.assertIn("theta = 0.4", result.stdout)
        self.assertIn("Gradient 1  (standard error 0)", result.stdout)

    def check_gradient(self, source, parameters, expected, draws=300, exact=False):
        result = Estimator(analyze(source), parameters).estimate(draws, seed=24)
        for name, target in expected.items():
            estimate = result["gradient"][name]
            tolerance = 1e-12 if exact else max(1e-10, 6 * estimate["standard_error"])
            self.assertAlmostEqual(estimate["mean"], target, delta=tolerance)
        return result

    def test_threshold_and_continuation(self):
        self.check_gradient("let u = uniform(0,1) in let y = if u < theta then 1 else 0 in 3*y",
                            {"theta": ".4"}, {"theta": 3}, exact=True)

    def test_outside_support(self):
        self.check_gradient("let u = uniform(0,1) in if u < theta then 1 else 0",
                            {"theta": "2"}, {"theta": 0}, exact=True)

    def test_nonlinear_continuation_and_negative_normal(self):
        self.check_gradient("let u = uniform(0,1) in let y = if theta <= u then 0 else 2 in y*y",
                            {"theta": ".4"}, {"theta": 4}, exact=True)

    def test_or_and_not(self):
        self.check_gradient("let x = uniform(0,1) in let y = uniform(0,1) in if not (theta <= x) || y < theta then 1 else 0",
                            {"theta": ".4"}, {"theta": 1.2}, draws=1200)

    def test_gaussian_mean_scale_and_multiple_parameters(self):
        mean, scale = .2, 1.3
        density = math.exp(-.5 * (mean / scale)**2) / math.sqrt(2 * math.pi)
        self.check_gradient("let x = gaussian(mu,sigma) in if x < 0 then 1 else 0",
                            {"mu": mean, "sigma": scale},
                            {"mu": -density / scale, "sigma": density * mean / scale**2}, exact=True)

    def test_interior(self):
        self.check_gradient("let x = gaussian(theta,1) in x*x", {"theta": ".7"}, {"theta": 1.4}, draws=1500)

    def test_continuous_kink(self):
        self.check_gradient("let u = uniform(0,1) in if u < theta then theta-u else 0",
                            {"theta": ".4"}, {"theta": .4}, draws=1200)

    def test_interior_and_boundary(self):
        result = self.check_gradient("let u = uniform(0,1) in if u < theta then theta else 0",
                                     {"theta": ".4"}, {"theta": .8}, draws=1200)
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], .4)

    def test_parameter_return(self):
        result = self.check_gradient("let u = uniform(0,1) in if u < theta then theta else 0",
                                     {"theta": ".5"}, {"theta": 1}, draws=1200)
        interior = result["interior"]["theta"]
        self.assertAlmostEqual(interior["mean"], .5, delta=6 * interior["standard_error"])
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], .5)

    def test_sample_return(self):
        result = self.check_gradient("let u = uniform(0,1) in if u < theta then u else 1",
                                     {"theta": ".4"}, {"theta": -.6}, exact=True)
        self.assertAlmostEqual(result["interior"]["theta"]["mean"], 0)
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], -.6)

    def test_reused_draw(self):
        result = self.check_gradient("let u = uniform(0,1) in if u + u < theta then theta else 1",
                                     {"theta": ".6"}, {"theta": .1}, draws=1200)
        interior = result["interior"]["theta"]
        self.assertAlmostEqual(interior["mean"], .3, delta=6 * interior["standard_error"])
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], -.2)

    def test_scaled_uniform(self):
        result = self.check_gradient("let u = uniform(0,2) in if u < theta then 1 else 0",
                                     {"theta": "1.2"}, {"theta": .5}, exact=True)
        self.assertAlmostEqual(result["interior"]["theta"]["mean"], 0)
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], .5)

    def test_moving_coefficient(self):
        result = self.check_gradient("let u = uniform(0,1) in if u * theta < 0.3 then 1 else 0",
                                     {"theta": ".6"}, {"theta": -5/6}, exact=True)
        self.assertAlmostEqual(result["interior"]["theta"]["mean"], 0)
        self.assertAlmostEqual(result["boundary"]["theta"]["mean"], -5/6)

    def test_independent_draws_upper_triangle(self):
        result = self.check_gradient("let u = uniform(0,1) in let v = uniform(0,1) in if u + v < theta then 1 else 0",
                                     {"theta": "1.5"}, {"theta": .5}, draws=1200)
        self.assertAlmostEqual(result["interior"]["theta"]["mean"], 0)
        boundary = result["boundary"]["theta"]
        self.assertAlmostEqual(boundary["mean"], .5, delta=6 * boundary["standard_error"])

    def test_oblique_hyperplane(self):
        self.check_gradient("let x = gaussian(0,1) in let y = gaussian(0,1) in if x+y < theta then 1 else 0",
                            {"theta": ".3"}, {"theta": math.exp(-.3**2 / 4) / math.sqrt(4 * math.pi)}, draws=1200)

    def test_uniform_triangle(self):
        self.check_gradient("let x = uniform(0,1) in let y = uniform(0,1) in if x+y < theta then 1 else 0",
                            {"theta": ".6"}, {"theta": .6}, draws=1200)

    def test_repeated_scaled_reversed_conditions(self):
        result = self.check_gradient("let u = uniform(0,1) in (if u < theta then 1 else 0) + (if 2*theta < 2*u then 0 else 2)",
                                     {"theta": ".4"}, {"theta": 3}, exact=True)
        self.assertEqual(result["surfaces"], 1)

    def test_boolean_and_nested_paths(self):
        self.check_gradient("let x = uniform(0,1) in let y = uniform(0,1) in if x < theta && y < theta then 1 else 0",
                            {"theta": ".4"}, {"theta": .8}, draws=1200)
        self.check_gradient("let x = uniform(0,1) in if x < theta then (if x < 0.2 then 1 else 2) else 0",
                            {"theta": ".4"}, {"theta": 2}, exact=True)

    def test_branch_local_samples(self):
        self.check_gradient("let x = uniform(0,1) in if x < theta then (let y = uniform(0,1) in y) else 0",
                            {"theta": ".4"}, {"theta": .5}, draws=1200)

    def test_polynomial_parameter_dependence(self):
        self.check_gradient("let u = uniform(0,1) in if u < theta*theta then 1 else 0",
                            {"theta": ".4"}, {"theta": .8}, exact=True)

    def test_rejections(self):
        cases = [
            ("let u = uniform(0,1) in if u*u < theta then 1 else 0", {"theta": ".4"}),
            ("if theta < 0 then 1 else 0", {"theta": ".4"}),
            ("let u = uniform(0,1) in if u < theta then 1 else 0", {"theta": "0"}),
            ("let x = gaussian(0,1) in if theta*x < 1 then 1 else 0", {"theta": "0"}),
            ("let x = gaussian(0,1) in (if x < theta then 1 else 0) + (if x < 2*theta then 1 else 0)", {"theta": "0"}),
            ("let x = gaussian(0,1) in 1/x", {}),
        ]
        for source, parameters in cases:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                Estimator(analyze(source), parameters)
        report = analyze("let u = uniform(0,1) in if u < theta then 1 else 0")
        report["candidates"][0]["solver"] = "unknown"
        with self.assertRaises(Unsupported):
            Estimator(report, {"theta": ".4"})


if __name__ == "__main__":
    unittest.main()
