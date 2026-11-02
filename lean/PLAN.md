# Lean formalization of the Kelvin–Voigt approximation paper

## 1. Scope, constraints, and completion

Formalize the theory in the compiled paper, using the sources in `paper/`, and place all project outputs under `lean/`. Leave the paper unchanged. Do not consult other local project folders for mathematical or implementation advice. Public sources and the agreed reference repositories may be used.

For GitHub publication, the repository root is the parent directory containing `paper/` and `lean/`. Repository configuration belongs at that root: `.gitignore` and the GitHub Actions workflows. Mathematical sources, verification tools and their results remain under `lean/`.

Include the actual continuum homogenization theorem, spectral representation, uniform approximation, dimension estimate, spectral-edge counterexample, and all supporting theory in the compiled appendices. Include the mathematical content of definitions, examples, remarks, and the exact identities in the numerical appendices. Exclude empirical performance claims, training experiments, and inactive appendix drafts.

The compiled appendix sources are `appendix_homogenized_tensors.tex`, `appendix_ua.tex`, `appendix_kv2d_details.tex`, and `appendix_cp_details.tex`. The long approximation draft, fractional draft, and separate counterexample draft are not additional specifications.

The initial inventory contains 17 numbered proved statements: Theorem 3.1, Proposition 3.3, Theorems 4.4 and 4.5, Proposition 4.7, and the results B.1–B.7 and B.9–B.13. In Appendix B, B.3, B.10, and B.13 are propositions, B.4 is a corollary, and the other proved statements are lemmas. Definition B.8 is also required. Audit the remaining numbered definitions, remarks, examples, introductory results, appendix derivations, and substantive unnumbered claims. Match introductory Results 1–3 to their detailed statements; treat the empirical Result 4 according to the experimental exclusion.

Completion requires concrete mathematical definitions, complete proofs of every included claim, a reproducible build, actual statement comparison and independent kernel validation, resolved referee findings, and an accurate coverage record. Abstract conditional theorems may be useful reusable components, but do not replace the paper's concrete results. The main neural approximation theorem may retain the paper's explicit A1/A2 hypotheses; the stated concrete architecture must satisfy its own separately proved admissibility and approximation claims.

Use Apache-2.0 for newly written code, preserving upstream licenses and attribution. Minimal documented repairs to subsidiary statements are authorized. Changes to a main mathematical conclusion, substantial hypotheses, or the paper's proof strategy require discussion with the user. Do not silently weaken statements.

Do not create or add checksum files, checksum manifests, SHA-256 digests, hashing scripts, project-file hashes, or hash-based artifact verification. Do not add optional provenance or source-revision hashes. The user has explicitly permitted only metadata required internally by Lean/Lake for dependency management and builds. Use release labels and source URLs in documentation.

Keep this plan at `lean/PLAN.md`. Maintain one compact `lean/STATUS.md` containing completed work, current blockers, next steps, commands actually run, validation outcomes, and referee resolutions. Keep the paper-to-Lean inventory in `formalization.yaml`, rather than duplicating it across multiple trackers. After compaction or resumption, read these records and the relevant source files before continuing. Preserve the specification and update status after each completed checkpoint.

## 2. Reusable mathematical organization

Use one Lake project, with project code under `KVApproximation`. Organize it by mathematical subject. Each subject must be usable with only its genuine transitive dependencies. Keep verification tools, manuscript-specific assembly, and experimental examples outside generic mathematical APIs.

| Subject | Public mathematical content |
| --- | --- |
| Analysis | Weak derivatives, Sobolev and evolution spaces, periodic function spaces, compactness, integration, and the required Laplace-transform results. |
| Tensor | Symmetric tensors, Frobenius inner products and norms, Mandel coordinates, and coercive coefficient fields. |
| OperatorTheory | Weighted Hilbert structures, orthogonal projections, variational operators, relaxation operators, exponentials, and resolvents. |
| Spectral | Bounded self-adjoint functional calculus, projection-valued measures, finite-dimensional tensor measures, support, variation, and convergence. |
| Homogenization | Periodic correctors, cell problems, static elasticity homogenization, and the evolution convergence argument. |
| Approximation | Analytic Chebyshev interpolation, logarithmic partitions, exponential-sum approximation, and complexity estimates. |
| Dynamics | Measurable-time ODE existence, uniqueness, continuation, invariant bounds, and perturbation estimates. |
| NeuralOperators | A1/A2 interfaces, architecture admissibility, approximation results, and finite-dimensional response models. |
| KelvinVoigt | The concrete coefficient class, constitutive operators, and assembly of the paper's main theorems. |
| Examples | Exact mathematical results used in the numerical appendices. |

Create `Numerics` only if a genuine body of reusable certified numerical results warrants it. A single fixed-constant certificate belongs next to its mathematical use in Approximation.

Use minimal file imports. A whole-project import may be provided for convenience, but generic results must not import it. Generic homogenization must not depend on neural approximation, manuscript examples, or verification machinery. Apply the same dependency discipline to every subject.

Use genuine Frobenius tensor norms and explicit weighted Hilbert-space structures or isometric equivalences. Do not rely on an incidental matrix or product norm that changes the paper's constants.

For reusable results, prove the general statement first where it follows the paper's argument, then supply the concrete specialization. Verify reuse by building small consumers containing a chosen subject and only its recursively required local sources, licenses, and external dependencies. This is a dependency-closure test, not a promise that a mathematical module has no prerequisites.

## 3. Toolchain, upstream foundations, and proof routes

At implementation start, recheck the latest stable, mutually compatible Lean, Mathlib, and LeanCert releases. The planning audit identified v4.35.0 for all three as the current compatible baseline. Freeze the selected versions for the proof. Do not move to a release candidate merely to obtain a newer auxiliary library.

Use the existing proof repositories as structural examples:
- https://github.com/jaumededios/Schiffer
- https://github.com/sgstepaniants/Forsythe

Reuse licensed, complete upstream source closures selectively. Do not import entire unrelated research libraries or copy unlicensed code. Preserve required attribution and include all source needed to rebuild the selected closures. Record source URLs and release labels or source dates without optional revision hashes.

The planning audit identified the following starting points:
- Tau Ceti: Sobolev W1p and evolution-space foundations; real Hilbert-space complexification and continuous functional calculus. The snapshot before the October 2026 move to Lean 4.36 release candidates uses Lean 4.35, although its Mathlib revision is newer than the 4.35 release tag. Compatibility must therefore be compiled and checked.
- Tau Ceti's newer BV compactness and Rellich–Kondrachov developments: selectively backport complete required closures if their assumptions fit. Its periodic Poincaré material is not a ready multidimensional torus elasticity theorem, and its Laplace-transform development does not supply all required uniqueness results.
- AIQ-Kitware/aiq-dkps-formalization: the small bounded self-adjoint Borel-calculus and PVM construction. The audited source uses a different Lean release, so port it together with the necessary real complexification bridge. Avoid conflicting duplicate Tau Ceti namespaces.
- Mathlib: Lax–Milgram, Fourier analysis on tori, operator exponentials, Riesz–Markov, vector-measure integration and variation, polynomial interpolation, and complex analysis.
- CoarseGraining and related homogenization work: consult selectively for applicable results; do not substitute scalar convex-domain results for the paper's vector elasticity theorem on its stated domains.

The audited real-functional-calculus closure comprises four source files. The bounded-PVM closure comprises six files: DiagonalMeasure, Polarization, Operator, Multiplicative, PVM, and ProjValMeasure.Basic. Initial source inspection found complete proof bodies, but compilation, compatibility, and dependency-axiom checks remain implementation work.

Follow these mathematical routes:

1. Establish the real weak Sobolev spaces, periodic zero-mean displacement space, Korn estimate, and closed symmetric-gradient range needed for the cell operators. Connect general variational results to the actual coefficient fields.

2. Prove static periodic elasticity homogenization and then the evolution homogenization result through the paper's Laplace-domain argument. Supply the required transform uniqueness and time-space bridges. Do not assume a homogenization principle as a replacement for Theorem 3.1.

3. Construct the weighted projections, their difference D, and the bounded coercive self-adjoint relaxation operator R. Prove the semigroup and resolvent identities used in Appendix A.

4. Obtain the spectral representation for arbitrary complete real Hilbert spaces through complexification and a bounded self-adjoint PVM. Infinite-dimensional PVM countable additivity is strong-operator additivity, not operator-norm additivity. Compress the PVM through the finite-dimensional D to obtain the tensor-valued measure and prove its support and Frobenius variation bounds. Use Mathlib's vector-measure integration where appropriate.

5. Prove the BV compactness, coefficient multiplication convergence, strong cell-operator convergence, tensor continuity, and weak spectral-measure convergence required by B.1–B.5. Supply the periodic and finite-component bridges rather than assuming them from scalar compactness.

6. Prove the Chebyshev estimate by the paper's analytic route: Joukowski pullback, coefficient decay on an annulus, a summable expansion, root-node aliasing, a geometric-tail estimate, and vector-valued duality. Prove the generic ellipse theorem before specializing to the paper's ellipse. Do not replace the interpolation argument with a different approximation construction.

7. Prove the required nonlinear measurable-time ODE theory and its application to the neural response. The audited Tau Ceti Carathéodory theorem is linear; Mathlib's usual Picard–Lindelöf theorem assumes continuous time. Neither alone supplies the nonlinear theorem for measurable strain derivatives.

8. Prove the general A1/A2 approximation argument and the concrete neural-operator architecture separately. Do not treat the architecture's universal approximation property as established merely because the abstract theorem assumes A1/A2.

## 4. Statements, correspondence, and numerical obligations

Before proving the manuscript results, write the concrete definitions and theorem statements, create the independent Comparator challenges, and review them against the compiled paper. Lock the main contracts and all numerical obligations before undertaking their proofs. Compatibility checks and construction of the definitions are preparatory work, not substitutes for this review.

Every reproduced numbered theorem, lemma, proposition, corollary, definition, example, or remark receives a docstring with its printed number, title where present, and TeX label or stable source location. For unnumbered statements, use the appendix/subsection and equation references; do not invent numbers. Supporting Lean lemmas identify the paper argument they support without falsely claiming a paper number.

Map proof stages to the paper's equations and reasoning steps. Record splits of one paper statement into multiple declarations, repeated statements, imported ingredients, and authorized corrections in the alignment section of `formalization.yaml`. Follow the paper's proof strategy; Lean-specific intermediate lemmas should expose its details.

The statement review must explicitly settle:
- The strain class on the entire nonnegative time axis, its W1-infinity bounds, and almost-everywhere derivatives.
- Actual PDE initial and boundary conditions and the paper's convergence topologies.
- The spectral interval [alpha_E / beta_V, beta_E / alpha_V].
- Tensor versus scalar state dimension and shared Prony rates.
- Interpolation degree m at least one, and the singleton spectral interval as a separate exact case.
- Signed Prony coefficient matrices; positivity of the spectral measure does not imply positivity of interpolatory coefficients.
- Empty coefficient classes without an unnecessary nonemptiness hypothesis.
- The difference between the full relaxation-operator spectrum and the support of the compressed memory measure.
- A uniform strict weighted-measure bound before taking a supremum.
- Equality in the ODE trapping-margin assumption, using the finite-time factor 1 - exp(-lambda_min t).

Preserve the paper's quantitative chain:
- Total variation of the spectral tensor measure is at most d_sym beta_V beta_E / alpha_E.
- The weighted measure has total variation at most d_sym (2 beta_V - alpha_V - beta_V alpha_E / beta_E), which is strictly less than 2 d_sym beta_V.
- The weighted response is entire in its spectral parameter and satisfies the paper's right-half-plane bound.
- The logarithmic partition has L = ceil(log(lambda_max / lambda_min)), mesh width at most one, and J = L + 1 in the nonsingleton case.
- The generic Chebyshev error bound is 4 M rho^(-(m-1)) / (rho-1), with rho > 1 and m >= 1.
- The paper's ellipse specialization uses rho = 2 and imaginary semiaxis 3/4.
- The uniform Prony estimate has constant kappa_IV = 8 d_sym (1 + sec(3/4)) delta_stress and decay 2^(-(m-1)).
- The internal-state perturbation bound is epsilon_G / lambda_min; the stress perturbation bound is epsilon_F + sqrt(n) epsilon_G / lambda_min.
- The dimension estimate uses d_sym J (1 + ceil(log2^+(kappa_IV / epsilon))); the singleton case uses d_sym states.

Use symbolic arguments, scaling, sharp support bounds, and exact arithmetic to avoid unnecessary interval subdivision or large computations. Preserve exact constants unless a stated bound requires a rational enclosure. The anticipated isolated LeanCert obligation is 7/10 < cos(3/4). Confirm its mathematical use during statement review. Use LeanCert in explicit kernel-trust mode; avoid unnecessary broad imports and native-trust shortcuts.

Document the subsidiary corrections and distinctions already identified:
- A merely locally Lipschitz lifting activation need not define a map on all L2 inputs. Use an appropriate global growth or global Lipschitz hypothesis for the corresponding concrete architecture claim.
- The thin-strip counterexample concerns the full relaxation operator's spectral edge, not the support of a possibly zero compressed memory measure.
- A coordinate change does not remove affine offsets in an experimental fit; the exact linear-surrogate identity applies after the stated offset removal.
- The numerical appendix's ratio of maximum to minimum operator norms is different from the coercivity contrast beta/alpha.
- Sampling descriptions with arbitrarily close control times do not automatically define one uniformly bounded strain class.
- Resolve typographical or typing inconsistencies using the detailed mathematical statements and record the clarification.

Include the exact appendix identities, including Mandel-coordinate transformations, the affine-surrogate coordinate reduction under its rank assumption, initial stress-free rotations, and determinant/exponential identities. Do not promote observed experimental behavior to a theorem.

## 5. Checkpoints, review, validation, and repository contents

Work through four checkpoints:

1. Establish the compatible toolchain and selected upstream source closures. Define and review the concrete statements and numerical obligations. Configure the Linux validation environment and test the sandboxed Comparator workflow on a small example before the large formalization depends on it.
2. Complete the reusable mathematical foundations and their consumer tests.
3. Prove the manuscript statements in dependency order and keep paper correspondence current.
4. Complete independent reviews, the full build, statement comparison, independent kernel checks, metadata validation, and final repository cleanup.

Use three independent referees and the applicable Tau Ceti standards:
- Mathematical fidelity: hypotheses, quantifiers, norms, constants, coverage, and correspondence to the paper's proof.
- Mathematical interfaces: correct concrete objects, generality, modular reuse, and dependency discipline.
- Proof and reproducibility: complete proof terms, axiom dependencies, tool trust, actual build evidence, and Comparator configuration.

Resolve substantive findings and record the resolution. Planning reviews are not evidence that future Lean code has passed review.

Use the current Comparator integrated into the selected Lean/Lake release. Keep independently reviewed challenge statements separate from solution declarations. Challenges must not import their solutions or use definition holes. Only the designated challenge theorem placeholders may remain unproved; they are excluded from the delivered proof library's axiom audit.

Run the authoritative Comparator checks on Linux with its sandbox enabled. GitHub Actions supplied the preserved partial results; after its allowance was exhausted, the user authorized completing the missing checks in the local Linux VM. Use the supported paranoid mode for independent kernel checking. If the configurations are divided among CI jobs or the local VM, verify complete coverage across their combined results. Keep VM images and caches under `lean/` as ignored artifacts. Do not use a sandbox-disabled run as the final validation evidence.

Compare every reproduced numbered proof statement and every substantive unnumbered exported result, grouped by subject. Comparator checks the Lean statements against one another; source correspondence and completeness still require the paper review.

Compile every delivered proof module, including modules that a convenience root might otherwise omit. Check that proof dependencies contain no `sorryAx`, custom axioms, or native-trust axioms. Permit only the standard Lean axioms required by the accepted mathematical foundation, including propext, Quot.sound, and Classical.choice.

Test the important boundaries: singleton spectrum, m = 1, zero memory, an empty material class, equality in the ODE margin, and infinite-dimensional bounded self-adjoint operators without compactness assumptions. Check the mathematical subject consumer builds.

Validate `formalization.yaml` against the current published schema. Record the source, alignment, main results, licenses, honest automation metadata, review status, and actual verification status. Follow https://github.com/mathlib-initiative/formalization.yaml and the applicable standards at https://github.com/TauCetiProject/TauCeti.

Preserve concise evidence of commands actually run, versions, modules or theorem names checked, outcomes, and resolved review findings. Do not label an unrun check successful. If code changes invalidate earlier evidence, rerun the affected checks. Pure prose cleanup does not by itself require repeating a previously successful Comparator run.

The final repository contains the mathematical source, necessary licensed upstream source, Lake configuration and required dependency metadata, license notices, a concise README, `formalization.yaml`, the minimal Comparator configuration and rerun scripts, this plan, and the compact status/verification record. Remove abandoned probes, redundant reports, unnecessary generated files, and prompt-like prose. Retain no added checksum or hash artifacts.

Do not mark the goal complete until all included mathematical claims and validation requirements are satisfied. Report genuine blockers precisely, preserve the completed work, and identify the missing prerequisite rather than reducing the target or treating an incomplete proof as complete.
