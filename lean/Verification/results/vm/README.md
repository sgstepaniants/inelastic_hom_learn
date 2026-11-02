# Local Linux validation

All **80 local Comparator configurations** passed with the default Linux
sandbox and `--paranoid`. Combined with the **251 preserved GitHub Actions
successes**, the suite covers **331 configurations and 702 selected
declarations**, with acceptance from all six kernels: Lean default, Lean
paranoid, lean4lean, nanoda, con-leche and con-ron.

The complete evidence is in `combined/`; `combined/coverage.json` reports
`passed: true`, with no missing, duplicate, unexpected or invalid records.
Each result has its complete per-configuration log. Original local results
are in `local/`, and the preserved CI inputs are in `../ci/`.

The Lima VM used Debian ARM Linux, four CPUs, 8 GiB RAM and the pinned Lean
4.35.0 toolchain. The bubblewrap isolation probe passed. On November 2,
2026, the full build passed all 4,282 jobs in 1,527.0 seconds; the transitive
axiom audit passed all 722 queries in 9.2 seconds, with only
`Classical.choice`, `Quot.sound` and `propext`. Complete records and logs are
`build.json`, `build.log`, `axioms.json` and `axioms.log`.

Three repaired pilot configurations ran serially:

| Configuration | Seconds | Selections |
| --- | ---: | ---: |
| `dirichlet_compactness` | 439.2 | 4 |
| `dirichlet_weak_compactness` | 405.8 | 1 |
| `homogenized_green` | 1,701.4 | 2 |

The other 77 comparisons ran with two concurrent workers. The full local
execution transcript is `runner.log`. Direct byte comparison confirmed
that all 1,085 proof and configuration files matched the workspace.

From `lean/`, validate the complete preserved evidence with:

```sh
python3 Verification/collect_comparator.py Verification/results/vm/combined
```

The complete suite passed without weakening the sandbox or omitting any
kernel. GitHub's earlier interrupted runs remain historical partial runs;
the combined evidence records the final successful validation.
