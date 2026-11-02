# Local Linux results

All **80 local Comparator configurations** passed with the default Linux sandbox
and `--paranoid`. Together with the 251 GitHub Actions results, they cover
**331 configurations and 702 selected declarations**. Every configuration was
accepted by Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron.

## Records

| Path | Contents |
| --- | --- |
| `combined/` | The 331 result/log pairs and complete `coverage.json`. |
| `local/` | The 80 local result/log pairs. |
| `../ci/` | The 251 GitHub Actions inputs. |
| `build.json`, `build.log` | Full build record and output. |
| `axioms.json`, `axioms.log` | Transitive axiom audit record and output. |
| `runner.log` | Local execution transcript. |

## Environment and execution

The Lima VM used Debian ARM Linux, four CPUs, 8 GiB RAM and Lean 4.35.0.
On November 2, 2026, the build passed 4,282 jobs in 1,527.0 seconds. The axiom
audit passed 722 queries in 9.2 seconds, reporting `Classical.choice`,
`Quot.sound` and `propext`.

The bubblewrap isolation probe passed. Three pilot configurations ran serially:

| Configuration | Seconds | Selections |
| --- | ---: | ---: |
| `dirichlet_compactness` | 439.2 | 4 |
| `dirichlet_weak_compactness` | 405.8 | 1 |
| `homogenized_green` | 1,701.4 | 2 |

The other 77 comparisons used two concurrent workers. Direct byte comparison
confirmed that the VM's 1,085 proof and configuration files matched the workspace.

From `lean/`, validate the combined collection with:

```sh
python3 Verification/collect_comparator.py Verification/results/vm/combined
```
