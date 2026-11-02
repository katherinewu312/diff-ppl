# Expectation gradients

From the repository root:

```sh
python3 gradient/estimate.py examples/symbolic/threshold.ppl --at theta=0.4 --draws 1000 --seed 0
```

For `.ppl` inputs, the command runs the analyzer automatically, keeping parameters
symbolic and passing its JSON directly to the estimator. Existing JSON reports
can also be supplied instead of a program. **Keep parameters symbolic when
generating those reports:** the analyzer's `--at` loses derivatives.
Repeat the estimator's `--at` for multiple parameters. Output contains the total,
interior, and boundary estimates in a concise text summary, each with a Monte
Carlo standard error.

### Testing
```
python3 -m unittest gradient.test_estimate -v
```
