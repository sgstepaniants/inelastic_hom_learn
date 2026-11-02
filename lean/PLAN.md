# Formalization scope and proof structure

## Scope

The formalization covers the mathematical theory in *Operator Learning of
Microstructure-Dependent Internal-Variable Models for Inelastic Homogenization:
Approximation and Complexity*. It includes continuum homogenization, spectral
representation, uniform approximation, the internal-state dimension estimate,
the spectral-edge counterexample, and the supporting theory in the compiled
appendices. Definitions, examples, remarks and exact identities in the numerical
appendices are included in the correspondence record.

The 17 numbered proof statements are Theorem 3.1, Proposition 3.3, Theorems 4.4
and 4.5, Proposition 4.7, and B.1–B.7 and B.9–B.13. In Appendix B, B.3, B.10 and
B.13 are propositions, B.4 is a corollary, and the other proof statements are
lemmas. Definition B.8 and the substantive unnumbered results are also included.
Introductory Results 1–3 correspond to the detailed theorems.

The compiled appendix sources are `appendix_homogenized_tensors.tex`,
`appendix_ua.tex`, `appendix_kv2d_details.tex` and `appendix_cp_details.tex`.
Empirical Result 4, training experiments, numerical performance observations
and inactive appendix drafts are outside the formalization.

The main approximation theorems use the paper's A1/A2 hypotheses. Separate
results establish admissibility and approximation for the specified neural
architecture. The main statements follow the paper's hypotheses, conclusions
and proof strategy; mathematical qualifications are listed below and in
[formalization.yaml](formalization.yaml).

## Library structure

The project uses one Lake package, with mathematical code under
`KVApproximation` and selected upstream sources under `Vendor`.

| Subject | Mathematical content |
| --- | --- |
| Analysis | Weak derivatives, Sobolev and evolution spaces, periodic function spaces, compactness and Laplace transforms. |
| Tensor | Symmetric tensors, Frobenius norms, Mandel coordinates and coercive coefficient fields. |
| OperatorTheory | Weighted Hilbert structures, projections, variational operators, relaxation operators, exponentials and resolvents. |
| Spectral | Functional calculus, projection-valued measures, tensor-valued measures, support, variation and convergence. |
| Homogenization | Periodic correctors, cell problems, static elasticity homogenization and evolution convergence. |
| Approximation | Chebyshev interpolation, logarithmic partitions, exponential-sum approximation and complexity estimates. |
| Dynamics | Measurable-time ODE existence, uniqueness, continuation, invariant bounds and perturbation estimates. |
| NeuralOperators | A1/A2 interfaces, architecture admissibility, approximation and finite-dimensional response models. |
| KelvinVoigt | Coefficient classes, constitutive operators and assembly of the paper's main theorems. |
| Examples | Mathematical identities used in the numerical appendices. |

General results and their specializations have separate modules. Imports follow
mathematical dependencies; the convenience root `KVApproximation` collects the
main results. Homogenization is independent of neural approximation, manuscript
examples and verification code. Consumer builds check each subject through its
recursive source and import dependencies.

Tensor estimates use the Frobenius norm. Weighted Hilbert-space structures and
isometric equivalences specify the norms used in operator and spectral arguments.

## Toolchain and foundations

Lean, Mathlib and LeanCert are pinned to **v4.35.0**. Lake's manifest records the
dependencies. Upstream sources are included with their required dependencies,
licenses and attribution in [Vendor/NOTICE.md](Vendor/NOTICE.md).

The principal foundations are:

- **Mathlib:** Lax–Milgram, Fourier analysis on tori, operator exponentials,
  Riesz–Markov, vector measures, variation, polynomial interpolation and complex
  analysis.
- **Tau Ceti:** Sobolev and evolution spaces, zero-boundary estimates,
  Fréchet–Kolmogorov and Rellich–Kondrachov compactness, real Hilbert-space
  complexification and continuous functional calculus.
- **AIQ–Kitware and Spectra:** bounded self-adjoint Borel functional calculus
  and projection-valued measures, adapted to the pinned toolchain.
- **Neural Network Proofs:** smooth-activation and ridge-approximation results.

[Schiffer](https://github.com/jaumededios/Schiffer) and
[Forsythe](https://github.com/sgstepaniants/Forsythe) supplied structural
references for the organization of the formalization.

## Proof structure

1. **Spatial analysis.** Weak Sobolev spaces, periodic zero-mean displacements,
   Korn estimates and the closed symmetric-gradient range connect variational
   operators to coefficient fields.
2. **Homogenization.** Static periodic elasticity homogenization identifies the
   Laplace-domain limits. Transform uniqueness and Sobolev realization recover
   the evolution equation, followed by Green/Duhamel forcing and whole-family
   convergence.
3. **Cell operators.** Weighted projections, their difference D, and the
   coercive self-adjoint relaxation operator R give the semigroup and resolvent
   identities in Appendix A.
4. **Spectral representation.** Complexification and the bounded self-adjoint
   PVM construction apply on complete real Hilbert spaces. Countable additivity
   holds in the strong operator topology. Compression through D gives the
   tensor-valued measure, its support and its Frobenius variation bounds.
5. **Continuity and compactness.** Periodic BV compactness and finite-component
   estimates yield coefficient compactness, multiplication convergence, strong
   cell-operator convergence, tensor continuity and weak spectral-measure
   convergence for B.1–B.5.
6. **Chebyshev approximation.** Joukowski pullback, annular coefficient decay,
   a summable Fourier expansion, root-node aliasing and vector-valued duality
   give the interpolation estimate. The generic ellipse result specializes to
   the ellipse used in the paper.
7. **Measurable-time dynamics.** A nonlinear Carathéodory construction handles
   measurable strain derivatives. Continuation, invariant bounds and
   perturbation estimates give the neural response results.
8. **Neural approximation.** Continuous Prony families yield approximation
   under A1/A2. Finite Fourier features and ridge approximation establish
   A1/A2 for the constant-bias architecture.

## Statement correspondence and quantitative bounds

[formalization.yaml](formalization.yaml) maps numbered statements, unnumbered
results and proof stages to Lean modules and declarations. Docstrings identify
paper numbers, TeX labels or section and equation references. The inventory also
records statements split across several declarations and the mathematical
qualifications used in the formalization.

The statements specify the nonnegative-time strain class, W¹,∞ bounds,
almost-everywhere derivatives, PDE initial and boundary conditions, and the
convergence topologies. They distinguish tensor and scalar state dimensions,
use shared Prony rates, and allow signed interpolation coefficients. Singleton
spectra, empty material classes, zero memory, m = 1 and equality in the ODE
trapping margin are included. The spectral results apply to bounded
self-adjoint operators on infinite-dimensional Hilbert spaces.

The quantitative estimates are:

- Spectral support: [alpha_E / beta_V, beta_E / alpha_V].
- Spectral tensor variation: at most d_sym beta_V beta_E / alpha_E.
- Weighted variation: at most
  d_sym (2 beta_V - alpha_V - beta_V alpha_E / beta_E), strictly below
  2 d_sym beta_V.
- The weighted response is entire in its spectral parameter and satisfies the
  paper's right-half-plane estimate.
- The logarithmic partition has L = ceil(log(lambda_max / lambda_min)),
  mesh width at most one and J = L + 1 for a nonsingleton interval.
- Chebyshev error: 4 M rho^(-(m-1)) / (rho-1), for rho > 1 and m >= 1.
- The paper's ellipse has rho = 2 and imaginary semiaxis 3/4.
- Prony error: kappa_IV 2^(-(m-1)), where
  kappa_IV = 8 d_sym (1 + sec(3/4)) delta_stress.
- Internal-state error: epsilon_G / lambda_min. Stress error:
  epsilon_F + sqrt(n) epsilon_G / lambda_min.
- Sufficient dimension: d_sym J (1 + ceil(log2^+(kappa_IV / epsilon))).
  A singleton spectrum requires d_sym states.

LeanCert proves 7/10 < cos(3/4) in kernel mode. The remaining estimates use
symbolic arguments and exact arithmetic.

## Mathematical qualifications

- Sobolev-bounded coefficient classes have compact L² closure. Compactness of
  the classes themselves also requires closedness, including at p = 1.
- The lifting activation is globally Lipschitz, ensuring a map on all L²
  inputs. The finite-dimensional output requires local Lipschitz regularity.
- The named approximation classes use a shared Fourier activation.
  `ActivatedFourierChain` also represents layer-dependent activations.
- The thin-strip counterexample concerns the spectrum of the full relaxation
  operator. The compressed memory measure can vanish for equal fields.
- The linear-surrogate coordinate identity applies after subtraction of affine
  offsets and under the stated rank assumption.
- The numerical appendix's ratio of operator norms and the coercivity contrast
  beta/alpha are distinct quantities.
- Sampling with arbitrarily close control times does not supply a common
  strain-rate bound over all sampled trajectories.
- The two-scale ansatz motivates the PDEs. An O(ε²) remainder theorem, specific
  activation implementations and crystal-plasticity evolution existence are
  outside the scope.

The appendix results include Mandel transformations, affine-surrogate
coordinates, stress-free initialization, rotations and determinant/exponential
identities.

## Verification and repository records

Verification consists of a full build, a transitive axiom audit, sandboxed
Comparator checks, independent kernel checks, subject consumer builds and
metadata validation. Three agent reviews covered mathematical fidelity,
interfaces and reproducibility. [STATUS.md](STATUS.md) records the results.

Comparator challenges have separate import dependencies from their solutions.
Definitions are fully specified; designated theorem placeholders occur in the
challenges. The proof-library audit accepts `propext`, `Quot.sound` and
`Classical.choice`. Comparator runs on Linux with the default sandbox and
`--paranoid`, using all six bundled kernels. Combined coverage accounts for
all configurations when execution is distributed across CI jobs or the local VM.

The full build includes every delivered proof module. Consumer builds check
subject reuse through isolated import paths. The metadata follows the published
[formalization.yaml schema](https://github.com/mathlib-initiative/formalization.yaml).
Source correspondence and review are recorded alongside the machine-checked
verification results.

Mathematical sources, validation tools and results are under `lean/`; manuscript
sources are under `paper/`. Repository configuration and GitHub workflows are at
the repository root. VM images and build caches are ignored artifacts. Project
code is Apache-2.0, with upstream licenses and notices retained. Dependency
metadata is supplied by Lean/Lake; source references use release labels and URLs.
