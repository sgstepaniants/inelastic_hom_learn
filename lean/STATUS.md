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
| Full proof libraries, challenges and convenience exports | After both repairs, the full Linux VM build passed: **4,282 jobs**, **1,527.0 seconds** |
| Production-artifact transitive axiom audit | **722 distinct queries/results**, only `propext`, `Classical.choice`, `Quot.sound`. The Linux VM audit after both repairs passed in **9.2 seconds** |
| Comparator selections covered by that audit | **702 declarations in 331 configurations**, plus twenty supporting definitions/ingredients |
| Isolated subject consumers | **10/10 passed**, including every module in each subject |
| Metadata | Published **v0.4 schema** passed; referenced local module paths exist |
| Sandboxed Comparator | **311 configurations / 657 theorem selections validated and preserved; full coverage pending** |
| Paranoid independent kernel checks | **All six kernels accepted every preserved configuration; 20 configurations still missing** |

The logs and machine-readable results are in [Verification/results/](Verification/results/). Rerun the full build and axiom audit with `python3 Verification/verify.py local`; rerun subject consumers with `python3 Verification/consumers.py`. The root import now exposes the main results, concrete architectures and exact appendix identities.

The consumer checks copy only a subject’s recursive source closure and licenses, then compile an importing file using only the corresponding production artifacts and external dependency/toolchain paths. They are import/reuse checks, not a second clean compilation of dependencies. Both referees’ path-isolation findings were fixed. All ten consumers were rerun successfully after the compactness and Green repairs, taking 86.8 seconds in total. **Homogenization imports all 72 subject modules through a 288-module local closure with no NeuralOperators, Approximation, KelvinVoigt or Examples dependency.** The other subjects passed the same check.

LeanCert proves `7/10 < cos(3/4)` in explicit kernel mode at Taylor depth 3. Source inspection finds no proof-library placeholders, custom axiom declarations or native-trust shortcuts. Designated challenge theorem placeholders remain separate from the proof library and its axiom audit.

## Remaining validation

GitHub Actions is the selected validation host at [sgstepaniants/inelastic_hom_learn](https://github.com/sgstepaniants/inelastic_hom_learn). The workflow uses Ubuntu 22.04, Lean 4.35.0, bubblewrap, and all six bundled kernels. It divides the 331 configurations / 702 selections into 16 disjoint shards with at most eight active jobs. Logs and result records are retained for 14 days. Actionlint, Python/Bash syntax checks, and six sharding/evidence regression tests passed.

[The first Actions run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41328491124) completed its Linux build in 4,387.6 seconds and its 722-declaration axiom audit in 6.9 seconds. The sandboxed paranoid pilot passed: `dimension_growth` (85.8 seconds), `tensor_bounds` (184.9 seconds), and `tensor_dimensions` (105.6 seconds). These are actual Comparator successes, but do not establish full coverage.

[The corrected Actions run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41347378153) passed its Linux build, 722-declaration axiom audit, shared-cache availability check, and seven-configuration sandboxed paranoid pilot (21 theorem selections). Its sixteen-shard matrix has now ended without complete coverage. It supersedes the cancelled first run; the remaining checks require recovery.

Several shards lost their runners during the Lean paranoid check of Dirichlet compactness or a result that depends on it. Their available logs end with a runner shutdown signal and exit 143, without a checker rejection. Completed shards 2, 3, 4, 13, 14 and 15, nineteen successes from shard 11, successful recovery jobs, recovered console-log results and two pilot results now provide **251 configurations / 549 selections**. The checked records, logs, original interrupted-job logs and an explicitly incomplete coverage report are preserved in [Verification/results/ci/](Verification/results/ci/). None of these configurations imports the compactness or Green modules changed by the repairs. Shards 6 and 12 have no downloadable job log or result artifact; no missing result is inferred to have passed.

A [15-minute resource sample](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41361668464) confirmed severe memory pressure: nearly all 8 GiB of RAM and about 6.7 GiB of swap were in use while the first kernel was still running. A [longer run with 12 GiB of extra swap](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41357483181) reached its time limit without completing the configuration. Local diagnostics isolated an expensive conversion in the private `W1p0.valueExtendByZeroL_apply` proof. The private measure cast now transports the vector directly as a continuous linear map, with proved norm and representative identities. All public statements and the compactness argument are unchanged.

After this repair, the helper checks in 52 milliseconds in the declaration diagnostic, and the bundled paranoid kernel completes module-only replay in **21.6 seconds**, using approximately **2.9 GiB** of resident memory. The full local rebuild, 722-declaration axiom audit and compiled-type comparisons for all **18 selections in ten affected configurations** passed. A subsequent local export of the four `dirichlet_compactness` selections and their full proof dependencies passed all six bundled kernels: Lean paranoid in **66.6 seconds**, Lean default in **69.8 seconds**, lean4lean in **76.0 seconds**, and the other three in under fourteen seconds each. These macOS preflights do not perform the sandboxed challenge comparison and are diagnostic evidence. Their records are in [Verification/results/compactness-replay/](Verification/results/compactness-replay/). None of the 251 preserved CI successes imports the changed module. Nine of the ten affected configurations have now passed the authoritative Linux recovery with all six kernels; `static_homogenization` remains in progress.

Shard 11 exposed a separate supporting-definition mismatch in `HomogenizedGreen.instDualNormedSpace`, before kernel checking began. The four Green dual-space instances now live in a shared interface-only module imported by both the independent challenge and the solution. No solution theorem is imported into its challenge, and all four selected theorem types in the three affected configurations still match. Comparator's own comparison function also accepts both Green statements and their complete supporting-declaration closure in a local diagnostic. The repaired Green configuration has now passed the authoritative sandboxed Linux comparison and all six kernels in **1,701.4 seconds**.

The repair checkpoint skipped the automatic full-suite push trigger. The published targeted recovery workflow is configured to rebuild and audit the updated libraries, check both compactness configurations and the Green interface, then run the other **77 missing configurations in eight disjoint batches**. Its final coverage job combines the preserved and new evidence and requires all **331 configurations / 702 selections** with all six kernels. Actionlint 1.7.12 and the six CI tests passed; its selection and aggregation scripts were exercised on the actual 251 preserved results.

The [earlier 34-configuration recovery run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41363120309) failed before any job started, including on one retry. The user subsequently confirmed that the GitHub Actions allowance had been exhausted.

The [repaired 80-configuration recovery run](https://github.com/sgstepaniants/inelastic_hom_learn/actions/runs/41372452886) encountered the same startup block on November 2 at 01:25 UTC. Its pilot and coverage jobs failed with no steps executed, and the eight-batch matrix was skipped. This run executed no proof checks. GitHub retries have stopped; the repository retains the recovery workflow and 251 valid saved results.

In the first run, the shared cache failed to save because the runner exhausted disk space. Several shards later lost their runners, and completed checks exposed statement mismatches. The revised workflow removes unused SDKs from disposable runners, requires a successfully saved shared cache before starting its shards, and streams detailed logs so an interrupted job retains its current checker stage. Its seven-configuration pilot includes the first repaired interfaces. The corrected run saved and verified the cache successfully, with 20 GiB available after its build.

Local compiled-type diagnostics now match all **331 configurations / 702 selections**, including universe-parameter names. Repairs align inferred scalar structures, local instance names, universe labels, and Carathéodory parameter order. The continuous-calculus challenge uses the standard complex-Hilbert-space calculus already used by its solution. The stress-bound challenge drops unused completeness and finite-dimensionality assumptions, retaining the stronger generality of the existing proof. Mathematical bounds and conclusions are unchanged. The full-target local rebuild and 722-declaration axiom audit passed after all edits, and the complete type diagnostic was repeated against the refreshed artifacts. The diagnostic is advisory: the complete authoritative sandboxed paranoid suite remains required before claiming completion.

On November 2 the user authorized local completion. The prepared Lima VM now runs Debian ARM Linux with four CPUs and 8 GiB RAM. Its relocated paths were repaired, the pinned Lean 4.35.0 toolchain and all six checker binaries installed, and the bubblewrap isolation probe passed. The full Linux rebuild and 722-query axiom audit passed. All three repaired pilot comparisons passed: `dirichlet_compactness` in **439.2 seconds**, `dirichlet_weak_compactness` in **405.8 seconds**, and `homogenized_green` in **1,701.4 seconds**. The runner then selected two concurrent checks. The latest saved checkpoint contains **60 local successes**, bringing the validated total to **311 configurations / 657 selections**. The remaining 20 checks are in progress, with no local failures; this checkpoint is not complete coverage.

`Verification/vm.sh` now preserves the CI results, fetches only the required Mathlib dependency closure, and invokes a resumable local recovery after the full build and axiom audit. After the serial pilot it permits up to two concurrent checks if their measured memory use fits the VM. Each successful local result is retained; the combined collector still requires every configuration and all six kernels. Ten runner/evidence tests passed, including preserving an earlier success when the next check fails, keeping parallel result logs separate, rejecting duplicate CI/local evidence and selecting transitive external cache dependencies. Local results and the combined report are copied into `Verification/results/vm/` when execution ends. No additional Comparator pass is claimed until its actual result is available.

Finish the local recovery, resolve any findings, and require the combined coverage report to pass before claiming complete Comparator validation.

Abandoned development probes, reference copies, isolated build artifacts and temporary consumer fixtures have been removed. The consumer script recreates its fixtures when rerun. The proof sources, licenses, required Lake metadata, challenges, verification scripts/results, README, inventory, plan and status remain. Build caches and the prepared VM are retained for the outstanding validation. Do not mark the goal complete while that validation remains outstanding.
