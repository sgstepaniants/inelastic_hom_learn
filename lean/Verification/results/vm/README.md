# Local Linux validation

The local Lima VM runs Debian ARM Linux with four CPUs, 8 GiB RAM and the
pinned Lean 4.35.0 toolchain. The bubblewrap isolation probe passed.

On November 2, 2026, the complete build passed all 4,282 jobs in 1,527.0
seconds. The transitive axiom audit passed all 722 queries in 9.2 seconds,
using only `Classical.choice`, `Quot.sound` and `propext`. The records and
complete logs are `build.json`, `build.log`, `axioms.json` and `axioms.log`.

The remaining Comparator checks are running. Their results are separate
from the 251 preserved CI successes in `../ci/`. A complete validation
requires a successful combined coverage report for all 331 configurations,
702 selections and all six kernels; the build and audit alone do not
establish that result.
