# Formalization and verification

Verified on November 2, 2026 with Lean, Mathlib and LeanCert **v4.35.0**.

The formalization covers 17 numbered proof statements and the supporting theory
listed in [PLAN.md](PLAN.md). All **331 Comparator configurations and 702 selected
declarations** passed the sandboxed Linux comparison and all six bundled kernels.
[formalization.yaml](formalization.yaml) gives the paper-to-Lean correspondence.
[MainResults.lean](KVApproximation/MainResults.lean) collects the five main
statements in paper order, with short proofs invoking the original declarations.

## Mathematical coverage

- **Theorem 3.1:** microscopic and homogenized existence and uniqueness, and
  whole-family weak H¹ convergence. The proof combines static periodic
  elasticity, Laplace-domain identification, Sobolev realization and
  Green/Duhamel forcing. `Homogenization.ForcedSubsequence` contains the
  compactness and identification argument; `KelvinVoigt.Homogenization`
  assembles the paper's theorem.
- **Proposition 3.3:** tensor spectral representation, spectral support,
  Frobenius variation bounds and uniqueness. The Hilbert-space PVM is
  countably additive in the strong operator topology.
- **Theorems 4.4–4.5:** uniform response approximation under A1/A2 and the
  internal-state dimension bound, including shared rates, signed Prony
  coefficients, strict uniform error, singleton spectra and dimension
  asymptotics.
- **Proposition 4.7:** an admissible strip family converges in L² material
  topology and both L¹ coefficient norms while the relaxation-operator
  spectral edge changes from two to one.
- **Appendix B:** B.1–B.7 and B.9–B.13, with Definition B.8. These results cover
  BV compactness, operator and spectral-measure continuity, Chebyshev
  interpolation, Prony approximation and measurable-time dynamics.
- **Remark 4.1:** periodic distributional-gradient estimates give the additive
  BV bound for 1≤p≤∞. Smoother coefficient and material classes have compact
  L² closure; closed classes are compact. Empty classes and dimension zero
  are included.
- **Example 2.1 and Remarks 4.2–4.3:** the constant-bias Fourier architecture
  satisfies A1/A2. The library includes finite feedforward lifting/output
  networks, representative independence, L² hidden fields and local output
  regularity. Affine-only networks embed the linear class. Layer-dependent
  Fourier activations have a separate implementation. Generic architecture
  admissibility derives A2 from A1 and member regularity.
- **Appendices A, C and D:** displacement cell evolution and its constitutive
  law; Mandel, plane-stress, affine-surrogate, stress-free initialization,
  rotation and determinant/exponential identities. The inventory also records
  the alternative Prony constructions and supporting unnumbered results.

## Scope and assumptions

Sobolev-bounded coefficient classes have compact L² closure; compactness of the
classes themselves requires closedness, including at p=1. The nonlinear lifting
is globally Lipschitz to define a map on all L² inputs, while the
finite-dimensional output needs local Lipschitz regularity.

The approximation classes use a shared Fourier activation.
`ActivatedFourierChain` also represents layer-dependent activations. The
formalization covers the PDEs motivated by the two-scale ansatz; an O(ε²)
remainder theorem, empirical training claims, specific activation
implementations and crystal-plasticity evolution existence are outside its
scope. [PLAN.md](PLAN.md) gives the remaining mathematical qualifications.

Three agent reviews covered mathematical fidelity, interfaces and
reproducibility. Review and automation details are recorded in
[formalization.yaml](formalization.yaml).

## Verification results

| Check | Result | Record |
| --- | --- | --- |
| Proof libraries, challenges and root imports | 4,282 build jobs; 1,527.0 seconds on Linux | [Build](Verification/results/vm/build.json), [log](Verification/results/vm/build.log) |
| Transitive axiom audit | 722 distinct queries, including all 702 Comparator selections; 9.2 seconds | [Audit](Verification/results/vm/axioms.json), [log](Verification/results/vm/axioms.log) |
| Sandboxed Comparator | 331/331 configurations and 702/702 selected declarations | [Coverage](Verification/results/vm/combined/coverage.json) |
| Kernel checks | Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron accepted every configuration | [Results and logs](Verification/results/vm/combined/) |
| Subject consumer builds | 10/10 subjects; 86.8 seconds | [Consumers](Verification/results/consumers.json), [log](Verification/results/consumers.log) |
| Metadata | Published v0.4 schema, referenced paths and challenge import dependencies | [Metadata](Verification/results/metadata.json) |
| Verification scripts | 10/10 tests on both macOS and Linux | [Runner tests](Verification/results/runner-tests.json) |

The statement collection was checked locally on November 3, 2026. The
[native axiom audit](Verification/results/axioms.json) covers 727 declarations,
including the five collected results, and checks that their fully quantified
statement types agree exactly with the originals. The Comparator records above
refer to the original subject declarations.

The axiom audit reports `propext`, `Classical.choice` and `Quot.sound`.
LeanCert proves `7/10 < cos(3/4)` in kernel mode at Taylor depth 3. Comparator
challenges contain designated theorem placeholders and are separate from the
proof library and its axiom audit.

The combined evidence contains 251 GitHub Actions results and 80 local Linux
results. Each record is checked against the configuration's command, challenge
and solution modules, selected declarations, six kernel acceptance messages and
Comparator success message. The command is
`lake comparator --config=Comparator/<name>.json --paranoid` with the default
Linux sandbox. The [CI notes](Verification/results/ci/README.md) and
[local notes](Verification/results/vm/README.md) describe the runs.

The local run used Debian ARM Linux in a Lima VM with four CPUs and 8 GiB RAM.
Three pilot configurations ran serially, followed by two concurrent workers.
The VM's 1,085 proof and configuration files matched the workspace by direct
byte comparison.

Consumer builds copy each subject's source dependencies and licenses, then
compile an importing file through isolated library paths using production
artifacts. Homogenization imports 72 subject modules through 288 local modules,
independently of NeuralOperators, Approximation, KelvinVoigt and Examples.
The full library build compiles the dependencies.

## Implementation notes

The vendored Rellich–Kondrachov implementation transports an Lp vector across a
measure equality through a continuous linear map, with norm and representative
identities. This avoids expensive conversion in the extension-by-zero operator.
The ten configurations using this implementation passed all kernel checks.

Four Green dual-space instance definitions are shared by the challenge and
solution through an interface module. The three configurations using these
instances passed all kernel checks. The 251 CI configurations are independent of
these modules and the modified compactness module.

## Reproduction

From `lean/`, with the pinned toolchain:

```sh
python3 Verification/verify.py local
python3 Verification/consumers.py
python3 Verification/test_ci.py
```

On Linux with bubblewrap:

```sh
python3 Verification/verify.py comparator
```

To validate the saved combined results:

```sh
python3 Verification/collect_comparator.py Verification/results/vm/combined
```

The collector requires one result/log pair per configuration. Historical copies
in descendant directories are counted as duplicates, so each run or combined
collection has its own directory.

The prepared macOS/Lima environment uses `bash Verification/vm.sh` to copy the
sources, rebuild, audit and resume comparisons. A proof edit requires rerunning
the affected configurations. The [README](README.md) describes the GitHub and
local execution options.
