# GitHub Actions results

This directory contains **251 configurations and 549 selected declarations**
that passed sandboxed Comparator and all six kernel checks. The remaining 80
configurations were completed in the local Linux VM. The
[combined coverage report](../vm/combined/coverage.json) contains all 331
configurations and 702 declarations.

## Source runs

| Run | Configurations |
| --- | ---: |
| [Main run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41347378153) | 193 |
| [First recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41359484670) | 30 |
| [Second recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41360863053) | 15 |
| [Third recovery](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41361562095) | 13 |

The main run supplied the completed shards 2, 3, 4, 13, 14 and 15; nineteen
results from shard 11; forty-nine results from the streamed logs of interrupted
shards 0, 1, 5, 7, 8, 9 and 10; and the pilot results for
`constant_spatial_form` and `global_positive_interpolation`.

Recovered records contain the per-configuration output and final JSON result
from the streamed job logs. Standalone logs omit GitHub's timestamp prefixes;
the original logs are retained under `job-logs/`.

The collector checks each record's command, challenge and solution modules,
selected declarations, six kernel acceptance messages and Comparator success
message. These CI configurations are independent of the compactness and Green
modules modified during validation.

`coverage.json` describes this 251-configuration CI subset. From `lean/`, check
the complete combined collection with:

```sh
python3 Verification/collect_comparator.py Verification/results/vm/combined
```
