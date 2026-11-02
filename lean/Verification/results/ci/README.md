# Partial Comparator evidence

As of November 2, 2026, this directory contains **251 configurations / 549 theorem selections** with successful sandboxed Comparator results and acceptance from all six kernels. `coverage.json` deliberately reports incomplete coverage: **80 configurations remain missing**.

The evidence comes from these GitHub Actions runs:

- [Main run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41347378153): completed shards 2, 3, 4, 13, 14 and 15; 19 successful checks from shard 11; 49 completed checks recovered from interrupted shards 0, 1, 5, 7, 8, 9 and 10; and two corrected-pilot checks (`constant_spatial_form` and `global_positive_interpolation`) whose full-shard logs were unavailable. The main run has ended without complete coverage. Shard 11's unsuccessful Green comparison is excluded.
- [First recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41359484670): 30 configurations.
- [Second recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41360863053): 15 configurations.
- [Third recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41361562095): 13 configurations.

Recovered records include the complete per-configuration output and final JSON result from the original streamed job logs. Their standalone logs omit GitHub's timestamp prefixes; the original job logs are retained under `job-logs/`.

Every saved result has been checked against the current configuration's exact command, challenge module, solution module and theorem selections, with all six acceptance messages and the final Comparator success message. These configurations do not import the Sobolev compactness module or Green modules changed by the pending repairs.

From `lean/`, inspect complete coverage with:

```sh
python3 Verification/collect_comparator.py Verification/results/ci
```

The command currently exits unsuccessfully because coverage is incomplete. None of these partial results establishes completion of the full suite.
