# Formalization status

Updated: 2026-11-01.

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
| Full proof libraries, challenges and convenience exports | Passed: **4,281 jobs**, **158.8 seconds** |
| Production-artifact transitive axiom audit | Passed: **722 distinct queries/results**, **92.1 seconds**, only `propext`, `Classical.choice`, `Quot.sound` |
| Comparator selections covered by that audit | **702 declarations in 331 configurations**, plus twenty supporting definitions/ingredients |
| Isolated subject consumers | **10/10 passed**, including every module in each subject |
| Metadata | Published **v0.4 schema** passed; referenced local module paths exist |
| Sandboxed Comparator | **Not run** |
| Paranoid independent kernel checks | **Not run** |

The logs and machine-readable results are in [Verification/results/](Verification/results/). Rerun the full build and axiom audit with `python3 Verification/verify.py local`; rerun subject consumers with `python3 Verification/consumers.py`. The root import now exposes the main results, concrete architectures and exact appendix identities.

The consumer checks copy only a subject’s recursive source closure and licenses, then compile an importing file using only the corresponding production artifacts and external dependency/toolchain paths. They are import/reuse checks, not a second clean compilation of dependencies. Both referees’ path-isolation findings were fixed and all ten consumers rerun. **Homogenization imports all 71 subject modules through a 287-module local closure with no NeuralOperators, Approximation, KelvinVoigt or Examples dependency.** The other subjects passed the same check.

LeanCert proves `7/10 < cos(3/4)` in explicit kernel mode at Taylor depth 3. Source inspection finds no proof-library placeholders, custom axiom declarations or native-trust shortcuts. Designated challenge theorem placeholders remain separate from the proof library and its axiom audit.

## Remaining validation

GitHub Actions is now the selected validation host. The parent `.gitignore` excludes local VM images, Lean/toolchain caches, build output and temporary files while retaining the proof sources, Lake manifest, Comparator configurations, proof-validation records and manuscript files. Git's ignore matcher passed all nine exclusion and eighteen retention checks. The current eligible files total **12.51 MiB**; the largest is `paper/main.pdf` at **1.59 MiB**. The GitHub repository URL is pending; no workflow has run yet.

The user started the Linux VM. Lima's host log confirms a running VM, a working SSH server and completed boot requirements. Its SSH configuration and runtime sockets now exist. Lima's status query still cannot read the macOS boot-session identifier inside the tool sandbox, so that query alone does not describe the running VM correctly.

The current obstacle is access from this session: both the SSH control socket and the loopback TCP connection return `Operation not permitted`. The permission system rejected an elevated SSH request because sandbox approvals are disabled. The mathematical sources and all successful local validation results remain unchanged.

`Verification/vm.sh` prepares the pinned toolchain and bubblewrap in the VM, runs all Comparator configurations with the default sandbox and `--paranoid`, and copies their logs and results back. The runner review identified stale source/configuration files, stale results after interrupted reruns, and inherited toolchain overrides. These have been corrected: the managed VM source trees are refreshed, Comparator records are cleared before reruns, and Lean overrides are unset. The referee's follow-up source review found no remaining blocking runner defect. Bash/Python syntax and an isolated simulated-failure check passed; the latter confirmed early stopping, stale-record removal, unchanged sandbox/paranoid arguments, and preservation of unrelated build evidence. These are runner checks, not Comparator executions. The user has now started the runner in Terminal, and Verification/results/vm.log records actual Debian Linux package provisioning. Comparator has not yet started. Direct SSH and process inspection remain unavailable in the tool sandbox, so progress is observed through the local run log. The launch command is:

```sh
cd /Users/georgestepaniants/Research/kv_approximation/lean
bash Verification/vm.sh
```

Inspect the resulting Comparator logs, resolve any findings, and rerun affected checks. No Comparator success is claimed before those executions complete.

Abandoned development probes, reference copies, isolated build artifacts and temporary consumer fixtures have been removed. The consumer script recreates its fixtures when rerun. The proof sources, licenses, required Lake metadata, challenges, verification scripts/results, README, inventory, plan and status remain. Build caches and the prepared VM are retained for the outstanding validation. Do not mark the goal complete while that validation remains outstanding.
