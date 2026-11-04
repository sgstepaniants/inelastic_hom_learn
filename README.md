# Operator Learning for Inelastic Homogenization

Lean formalization for **Operator Learning of
Microstructure-Dependent Internal-Variable Models for Inelastic Homogenization:
Approximation and Complexity**, by **Lianghao Cao, George Stepaniants, and
Andrew M. Stuart**.

The project studies how recurrent neural operators can represent homogenized
constitutive laws using a finite set of internal variables to encode loading
history. For periodic Kelvin–Voigt viscoelasticity, the theory connects
homogenization and spectral representations of memory kernels to uniform
approximation guarantees and explicit bounds on the required internal-variable
dimension. The manuscript also presents numerical experiments on viscoelasticity
and finite-deformation crystal plasticity.

[Main results](lean/KVApproximation/MainResults.lean) ·
[Reader's guide](lean/READER_GUIDE.md) · [Lean documentation](lean/README.md) ·
[Formalization status](lean/STATUS.md)

## Repository contents

| Path | Contents |
| --- | --- |
| `paper/` | Reserved for the final paper. |
| [`lean/KVApproximation/MainResults.lean`](lean/KVApproximation/MainResults.lean) | The five main statements in paper order, with explicit hypotheses and short proofs invoking the original results. |
| [`lean/KVApproximation/`](lean/KVApproximation/) | Proof library for analysis, tensors, operator and spectral theory, homogenization, approximation, dynamics, neural operators, and examples. |
| [`lean/Comparator/`](lean/Comparator/) | Separate challenge statements and Comparator configurations. |
| [`lean/Verification/`](lean/Verification/) | Build, axiom-audit, and reuse checks, with recorded validation results. |
| [`lean/Vendor/`](lean/Vendor/) | Selected upstream Lean sources with attribution. |
| [`lean/formalization.yaml`](lean/formalization.yaml) | Correspondence between manuscript statements and Lean declarations. |

## Build the Lean formalization

The project pins Lean, Mathlib, and LeanCert to **v4.35.0**. With the Elan
toolchain manager installed, run from the repository root:

```sh
cd lean
lake build KVApproximation Challenges TauCeti ForTauCeti NeuralNetworkProofs
```

The toolchain and dependencies are specified in
[`lean/lean-toolchain`](lean/lean-toolchain),
[`lean/lakefile.toml`](lean/lakefile.toml), and
[`lean/lake-manifest.json`](lean/lake-manifest.json).

To use the main results in Lean:

```lean
import KVApproximation
```

Individual modules can also be imported; see the
[Lean README](lean/README.md) for examples and module organization.
The five main statements can be read and checked together in
[MainResults.lean](lean/KVApproximation/MainResults.lean). Their original
declarations and detailed proofs remain in the subject modules.

## Verification

The [reader's guide](lean/READER_GUIDE.md) describes the mathematical review:
the statements and definitions, together with the recorded proof checks.

From `lean/`, use Python 3 to run the full build and transitive axiom audit:

```sh
python3 Verification/verify.py local
```

After building, check isolated subject reuse with:

```sh
python3 Verification/consumers.py
```

The recorded Linux validation passed the full build, the 722-declaration
transitive axiom audit limited to `propext`, `Classical.choice`, and `Quot.sound`,
and all ten subject consumers. **All 331 Comparator configurations / 702 selected declarations passed
the sandboxed Linux comparison and all six bundled kernels.** The
[complete coverage report](lean/Verification/results/vm/combined/coverage.json)
combines 251 GitHub Actions successes with 80 local Linux successes. See
[`lean/STATUS.md`](lean/STATUS.md) for proof coverage and verification methods.

The [current native axiom audit](lean/Verification/results/axioms.json) covers
727 declarations, including the five collected main results, and checks that
their statement types agree exactly with the original declarations.

On Linux with bubblewrap, run the sandboxed checks from `lean/`:

```sh
python3 Verification/verify.py comparator
```

Validation logs and machine-readable results are stored in
[`lean/Verification/results/`](lean/Verification/results/).

## Manuscript

The final paper will be added to `paper/`. The folder is currently empty.

## Licensing

The project Lean code is licensed under [Apache-2.0](lean/LICENSE). Vendored sources
retain their upstream licenses and attribution; see
[`lean/Vendor/NOTICE.md`](lean/Vendor/NOTICE.md).
