# Local Linux validation

The local Lima VM runs Debian ARM Linux with four CPUs, 8 GiB RAM and the
pinned Lean 4.35.0 toolchain. The bubblewrap isolation probe passed.

On November 2, 2026, the complete build passed all 4,282 jobs in 1,527.0
seconds. The transitive axiom audit passed all 722 queries in 9.2 seconds,
using only `Classical.choice`, `Quot.sound` and `propext`. The records and
complete logs are `build.json`, `build.log`, `axioms.json` and `axioms.log`.

Four sandboxed Comparator configurations have passed with `--paranoid`
and all six kernels:

| Configuration | Seconds | Selections |
| --- | ---: | ---: |
| `dirichlet_compactness` | 439.2 | 4 |
| `dirichlet_weak_compactness` | 405.8 | 1 |
| `homogenized_green` | 1,701.4 | 2 |
| `bernstein_geometry` | 74.9 | 5 |

Their records and complete logs are in `local/`. Combining them with the
251 preserved CI successes in `../ci/` validates **255 configurations and
561 selections**. The checked union is in `combined/`; its coverage report
explicitly records the 76 missing configurations and `passed: false`.

The remaining checks are running two at a time. Complete validation requires
a successful combined coverage report for all 331 configurations, 702
selections and all six kernels.
