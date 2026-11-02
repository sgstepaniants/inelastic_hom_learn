# Formalization status

Updated: 2026-11-02.

[PLAN.md](PLAN.md) controls the scope; [formalization.yaml](formalization.yaml) records source correspondence. All 17 numbered proof statements and the included unnumbered theory have compiled implementations. All 331 Comparator configurations and 702 selected declarations have passed the sandboxed Linux comparison and all six bundled kernels.

All outputs remain under `lean/`; `paper/` is unchanged. No project checksums, hash manifests, digest scripts or optional provenance hashes are permitted. Lean/Lake’s required internal metadata is the sole exception.

## Completed theory

- **Theorem 3.1:** actual continuum homogenization, microscopic and homogenized existence and uniqueness, and whole-family weak H¹ convergence. The proof follows static periodic elasticity, Laplace-domain identification, time-domain recovery and Green/Duhamel forcing. `Homogenization.ForcedSubsequence` is independently reusable; `KelvinVoigt.Homogenization` retains the original paper contract.
- **Proposition 3.3:** the actual tensor spectral representation, support, Frobenius variation bound and uniqueness. The Hilbert-space PVM has strong-operator countable additivity.
- **Theorems 4.4–4.5:** uniform response approximation and the exact internal-state dimension bound under A1/A2, including shared rates, signed Prony coefficients, strict uniform error, singleton spectra and dimension asymptotics.
- **Proposition 4.7:** the fixed admissible strip family converges in the actual L² material topology and both L¹ coefficient norms, while the full relaxation-operator spectral edge changes from two to one.
- **Appendix B:** all numbered proof statements B.1–B.7 and B.9–B.13, with Definition B.8. This includes BV compactness, operator and spectral-measure continuity, analytic Chebyshev interpolation, Prony approximation and measurable-time internal-variable dynamics.
- **Remark 4.1:** periodic distributional-gradient bounds imply the exact additive BV estimate for 1≤p≤∞. Smoother coefficient and material classes have compact L² closure; closed classes are compact. Endpoint exponents, empty classes and dimension zero are retained.
- **Example 2.1 and Remarks 4.2–4.3:** the actual constant-bias Fourier mapping satisfies A1/A2. Finite feedforward lifting/output networks, representative independence, actual L² hidden fields and local output regularity are proved. Affine-only networks embed the linear class exactly and retain the same A1/A2 approximators. Independently activated Fourier chains are also implemented. Generic architecture admissibility derives A2 from A1 and member regularity without changing the approximator.
- **Active Appendices A, C and D:** displacement cell evolution and its constitutive law; exact Mandel, plane-stress, offset-subtracted surrogate, stress-free initialization, rotation, determinant and exponential identities. Alternative Prony constructions and the other substantive unnumbered claims are recorded in the inventory.

## Source review

Three independent referees covered mathematical fidelity, interfaces and reuse, and proof/reproducibility. New contracts were reviewed before their proofs. The final coverage review found no further substantive theorem omission in the agreed compiled-paper scope. The following qualifications remain explicit:

- Smoother classes have compact **closure**; compactness of the original class requires closedness, including at p=1.
- A globally Lipschitz nonlinear lifting supplies the growth control needed on all L² inputs. The finite-dimensional output needs only local Lipschitz regularity. This is the subsidiary correction authorized in PLAN.md.
- The approximation classes use a shared Fourier activation. `ActivatedFourierChain` covers the broader layer-dependent definition and its regularity as a reusable component.
- The formal two-scale ansatz motivates the PDEs; no O(ε²) remainder expansion is asserted. Empirical sampling/training claims, specific activation implementations and crystal-plasticity evolution existence are outside the agreed theory.

Earlier findings about C∞ versus analytic generators, Frobenius norms, signed interpolation coefficients, strict uniform measure bounds, equality in the ODE trapping margin and full spectrum versus compressed memory support are resolved. Ordinary declaration kernel checking remains enabled throughout.

## Validation

Lean, Mathlib and LeanCert are pinned to **v4.35.0**. Verification completed on November 2, 2026.

| Check | Actual result | Evidence |
| --- | --- | --- |
| Full proof libraries, challenges and convenience exports | **4,282 build jobs passed** in 1,527.0 seconds on Linux, after the repairs | [Build record](Verification/results/vm/build.json), [log](Verification/results/vm/build.log) |
| Transitive axiom audit | **722 distinct queries/results**, including all 702 Comparator selections; only `propext`, `Classical.choice`, `Quot.sound`; 9.2 seconds | [Audit record](Verification/results/vm/axioms.json), [log](Verification/results/vm/axioms.log) |
| Sandboxed Comparator | **331/331 configurations; 702/702 selected declarations; no missing, duplicate, unexpected or invalid records** | [Combined coverage](Verification/results/vm/combined/coverage.json) |
| Independent kernels | Every configuration accepted by **Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron** | Per-configuration records and complete logs in [combined/](Verification/results/vm/combined/) |
| Isolated subject consumers | **10/10 passed** after the repairs, in 86.8 seconds total | [Consumer record](Verification/results/consumers.json), [log](Verification/results/consumers.log) |
| Metadata and challenge separation | Published **v0.4 schema** passed; referenced paths exist; no challenge transitively imports its solution module | [Metadata record](Verification/results/metadata.json) |

The combined Comparator evidence consists of **251 preserved GitHub Actions successes and 80 local Linux successes**. Every record was checked against the current configuration's exact command, challenge and solution modules, selected declarations, six acceptance messages and final Comparator success message. All commands use `lake comparator --config=Comparator/<name>.json --paranoid` with the default Linux sandbox.

The local run used Debian ARM Linux in the Lima `proof` VM, with four CPUs and 8 GiB RAM. The bubblewrap isolation probe passed. The runner rebuilt all libraries and audited their axioms, ran the three repaired pilots serially, then used two concurrent comparisons. Direct byte comparison confirmed that all 1,085 proof and configuration files in the VM matched the workspace. No project hashes or checksum manifests were generated.

Consumer checks copy each subject's recursive source closure and licenses, then compile its importing file using only the corresponding production artifacts and external dependency/toolchain paths. They test dependency closure and reuse; the full build compiles all dependencies. **Homogenization imports all 72 subject modules through a 288-module local closure with no NeuralOperators, Approximation, KelvinVoigt or Examples dependency.** Both reviewers' path-isolation findings were fixed before the successful rerun.

LeanCert proves `7/10 < cos(3/4)` in explicit kernel mode at Taylor depth 3. Proof-library source inspection found no placeholders, custom axiom declarations or native-trust shortcuts. Designated challenge theorem placeholders remain separate from the proof library and its axiom audit.

## Resolved validation findings

- **Statement and supporting-definition mismatches:** challenges were aligned with the reviewed production contracts, including scalar structures, local instances, universe labels and Carathéodory parameter order. The continuous-calculus challenge uses the existing complex-Hilbert-space calculus; the stress-bound challenge retains the solution's stronger generality by omitting unused assumptions. Main mathematical bounds and conclusions are unchanged.
- **Compactness replay performance:** a private measure cast in the vendored Rellich–Kondrachov implementation forced expensive conversion while checking the extension-by-zero operator. It now transports the Lp vector directly through a continuous linear map, with proved norm and representative identities. Public statements and the compactness argument are unchanged. All ten affected configurations passed the full sandboxed six-kernel checks.
- **Green dual-space interface:** the challenge and solution had different supporting definitions for a local normed-space instance. Four shared instance definitions now live in an interface-only module, with no solution theorem imported by its challenge. All three affected configurations passed.
- **Interrupted GitHub runners and exhausted allowance:** completed checks were recovered from artifacts and full streamed logs. The user authorized local completion after the Actions allowance was exhausted. No failed or unexecuted check was counted as a pass. The preserved CI configurations do not import the repaired compactness or Green modules.

The [CI evidence notes](Verification/results/ci/README.md) identify the source Actions runs and explain recovered logs. The CI-only report remains incomplete by design; the [combined report](Verification/results/vm/combined/coverage.json) is the complete coverage record. The [local evidence notes](Verification/results/vm/README.md) describe the VM run.

## Reproduce validation

Run these commands from `lean/` with the pinned toolchain:

```sh
python3 Verification/verify.py local
python3 Verification/consumers.py
python3 Verification/test_ci.py
```

On Linux with bubblewrap, run the full Comparator suite:

```sh
python3 Verification/verify.py comparator
```

The full runner succeeds only after every configured comparison passes. For collected evidence, use a directory containing exactly one result pair per configuration; historical copies in descendant directories are deliberately rejected as duplicates. To check the preserved complete evidence:

```sh
python3 Verification/collect_comparator.py Verification/results/vm/combined
```

On the prepared macOS/Lima setup, `bash Verification/vm.sh` copies current sources, rebuilds and audits them, then resumes missing or failed comparisons. Preserve saved evidence only while proof sources remain unchanged; after an edit, rerun every affected configuration. The README documents GitHub and local execution options.

The [ten runner/evidence tests](Verification/results/runner-tests.json) passed on both macOS and Linux. They cover complete shard selection, rejection of missing, duplicate, stale or weakened evidence, preservation of earlier successes after a failure, separate parallel logs and the required external dependency-cache closure.

No validation remains outstanding for the agreed scope. Proof sources, licensed upstream closures, required Lake metadata, independent challenges, rerun tools and verification evidence are retained. Development probes and superseded diagnostic reports have been removed; ignored build caches and the prepared VM remain available for reproducibility.
