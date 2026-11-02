# Formalization status

Updated: 2026-11-02.

[PLAN.md](PLAN.md) controls the scope; [formalization.yaml](formalization.yaml) records source correspondence. All 17 numbered proof statements and the included unnumbered theory have compiled implementations. The project remains incomplete until sandboxed Comparator and its paranoid independent checkers have run successfully.

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

Lean, Mathlib and LeanCert are frozen at **v4.35.0**.

| Check | Actual result |
| --- | --- |
| Full proof libraries, challenges and convenience exports | Linux baseline passed: **4,281 jobs**, **1,998.7 seconds**. After the compactness repair, the full local rebuild passed in **188.5 seconds**; Linux refresh pending |
| Production-artifact transitive axiom audit | **722 distinct queries/results**, only `propext`, `Classical.choice`, `Quot.sound`. Linux baseline passed in **2.7 seconds**; audit after the repair passed locally in **10.5 seconds** |
| Comparator selections covered by that audit | **702 declarations in 331 configurations**, plus twenty supporting definitions/ingredients |
| Isolated subject consumers | **10/10 passed**, including every module in each subject |
| Metadata | Published **v0.4 schema** passed; referenced local module paths exist |
| Sandboxed Comparator | **192 configurations / 435 theorem selections validated and preserved; full coverage pending** |
| Paranoid independent kernel checks | **All six kernels accepted every preserved configuration; 139 configurations still missing** |

The logs and machine-readable results are in [Verification/results/](Verification/results/). Rerun the full build and axiom audit with `python3 Verification/verify.py local`; rerun subject consumers with `python3 Verification/consumers.py`. The root import now exposes the main results, concrete architectures and exact appendix identities.

The consumer checks copy only a subject’s recursive source closure and licenses, then compile an importing file using only the corresponding production artifacts and external dependency/toolchain paths. They are import/reuse checks, not a second clean compilation of dependencies. Both referees’ path-isolation findings were fixed and all ten consumers rerun. **Homogenization imports all 71 subject modules through a 287-module local closure with no NeuralOperators, Approximation, KelvinVoigt or Examples dependency.** The other subjects passed the same check.

LeanCert proves `7/10 < cos(3/4)` in explicit kernel mode at Taylor depth 3. Source inspection finds no proof-library placeholders, custom axiom declarations or native-trust shortcuts. Designated challenge theorem placeholders remain separate from the proof library and its axiom audit.

## Remaining validation

GitHub Actions is the selected validation host at [sgstepaniants/inelastic_hom_learn](https://github.com/sgstepaniants/inelastic_hom_learn). The workflow uses Ubuntu 22.04, Lean 4.35.0, bubblewrap, and all six bundled kernels. It divides the 331 configurations / 702 selections into 16 disjoint shards with at most eight active jobs. Logs and result records are retained for 14 days. Actionlint, Python/Bash syntax checks, and six sharding/evidence regression tests passed.

[The first Actions run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41328491124) completed its Linux build in 4,387.6 seconds and its 722-declaration axiom audit in 6.9 seconds. The sandboxed paranoid pilot passed: `dimension_growth` (85.8 seconds), `tensor_bounds` (184.9 seconds), and `tensor_dimensions` (105.6 seconds). These are actual Comparator successes, but do not establish full coverage.

[The corrected Actions run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41347378153) passed its Linux build, 722-declaration axiom audit, shared-cache availability check, and seven-configuration sandboxed paranoid pilot (21 theorem selections). The full matrix has started with eight concurrent jobs across sixteen shards. It supersedes the cancelled first run; complete coverage is still pending.

Several shards lost their runners during the Lean paranoid check of Dirichlet compactness or a result that depends on it. Their logs end with a runner shutdown signal and exit 143, without a checker rejection. Completed shards 2, 3, 4 and 15, successful recovery jobs, recovered console-log results and two pilot results now provide **192 configurations / 435 selections**. The checked records, logs, original interrupted-job logs and an explicitly incomplete coverage report are preserved in [Verification/results/ci/](Verification/results/ci/). None of these configurations imports the compactness module being refactored.

A [15-minute resource sample](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41361668464) confirmed severe memory pressure: nearly all 8 GiB of RAM and about 6.7 GiB of swap were in use while the first kernel was still running. A [longer run with 12 GiB of extra swap](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41357483181) reached its time limit without completing the configuration. Local diagnostics isolated an expensive conversion in the private `W1p0.valueExtendByZeroL_apply` proof. The private measure cast now transports the vector directly as a continuous linear map, with proved norm and representative identities. All public statements and the compactness argument are unchanged.

After this repair, the helper checks in 52 milliseconds in the declaration diagnostic, and the bundled paranoid kernel completes module-only replay in **21.6 seconds**, using approximately **2.9 GiB** of resident memory. The full local rebuild, 722-declaration axiom audit and compiled-type comparisons for all **18 selections in ten affected configurations** passed. The module-only replay trusts its compiled imports and is diagnostic evidence, not a substitute for sandboxed Comparator. Its records are in [Verification/results/compactness-replay/](Verification/results/compactness-replay/). None of the 192 preserved CI successes imports the changed module. All ten affected configurations still require authoritative Linux replay with all six kernels.

The repair checkpoint skips the automatic full-suite push trigger to preserve the useful jobs already running. A targeted recovery workflow must run the repaired configurations and all remaining missing checks; full coverage remains required.

The [next 34-configuration recovery run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41363120309) failed before any job started, including on one retry. Its reason is in an annotation unavailable through the connected GitHub tools; the user has been asked to provide that message. Existing jobs continue. No billing or runner-capacity cause is assumed without that annotation.

In the first run, the shared cache failed to save because the runner exhausted disk space. Several shards later lost their runners, and completed checks exposed statement mismatches. The revised workflow removes unused SDKs from disposable runners, requires a successfully saved shared cache before starting its shards, and streams detailed logs so an interrupted job retains its current checker stage. Its seven-configuration pilot includes the first repaired interfaces. The corrected run saved and verified the cache successfully, with 20 GiB available after its build.

Local compiled-type diagnostics now match all **331 configurations / 702 selections**, including universe-parameter names. Repairs align inferred scalar structures, local instance names, universe labels, and Carathéodory parameter order. The continuous-calculus challenge uses the standard complex-Hilbert-space calculus already used by its solution. The stress-bound challenge drops unused completeness and finite-dimensionality assumptions, retaining the stronger generality of the existing proof. Mathematical bounds and conclusions are unchanged. The full-target local rebuild and 722-declaration axiom audit passed after all edits, and the complete type diagnostic was repeated against the refreshed artifacts. The diagnostic is advisory: the complete authoritative sandboxed paranoid suite remains required before claiming completion.

The prepared Lima VM and `Verification/vm.sh` remain an alternative for local execution. Earlier VM access from the agent was blocked, and its saved log records package provisioning rather than a Comparator verdict. The runner refreshes its managed source copy, clears stale Comparator records, unsets Lean overrides, and retains the sandbox/paranoid settings. Its source review, syntax checks, and simulated failure-handling check passed; these are runner checks, not proof validation. The active validation now runs on GitHub Actions.

Inspect the Actions results, resolve any findings, and rerun affected checks. No Comparator success is claimed before those executions complete.

Abandoned development probes, reference copies, isolated build artifacts and temporary consumer fixtures have been removed. The consumer script recreates its fixtures when rerun. The proof sources, licenses, required Lake metadata, challenges, verification scripts/results, README, inventory, plan and status remain. Build caches and the prepared VM are retained for the outstanding validation. Do not mark the goal complete while that validation remains outstanding.
