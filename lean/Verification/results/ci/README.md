# Partial Comparator evidence

As of November 2, 2026, this directory contains **169 configurations / 383 theorem selections** with successful sandboxed Comparator results and acceptance from all six kernels. `coverage.json` deliberately reports incomplete coverage: **162 configurations remain missing**.

The evidence comes from these GitHub Actions runs:

- [Main run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41347378153): completed shards 2, 3 and 4; 46 completed checks recovered from interrupted shards 0, 1, 5, 7, 8 and 9; and two corrected-pilot checks (`constant_spatial_form` and `global_positive_interpolation`) whose full-shard logs were unavailable.
- [First recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41359484670): 30 configurations.
- [Second recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41360863053): 15 configurations.
- [Third recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41361562095): 13 configurations.

Recovered records include the complete per-configuration output and final JSON result from the original streamed job logs. Their standalone logs omit GitHub's timestamp prefixes; the original job logs are retained under `job-logs/`.

Every saved result has been checked against the current configuration's exact command, challenge module, solution module and theorem selections, with all six acceptance messages and the final Comparator success message. These configurations do not import the Sobolev compactness module currently being optimized for kernel replay.

From `lean/`, inspect complete coverage with:

```sh
python3 Verification/collect_comparator.py Verification/results/ci
```

The command currently exits unsuccessfully because coverage is incomplete. None of these partial results establishes completion of the full suite.
