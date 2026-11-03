# Reader's guide

The manual mathematical check is that the Lean statements and the definitions
they use express the intended mathematics. The recorded kernel checks establish
that those formal statements follow from the permitted axioms.

## Required and optional reading

For a selected result, the required mathematical review consists of:

1. Its complete [challenge statement](#statements-and-definitions), including
   hypotheses, quantifiers and implicit parameters.
2. Every definition-index row whose **Required for** column contains that
   result's number. These include definitions reached through other definitions,
   together with the relevant norm and inner-product instances.
3. Any [existence statement](#definitions-using-existence-results) marked for
   that result, where a definition uses `.choose` to select an object.

Follow the linked declarations, rather than reading their entire source files.
Read a definition's formula or construction and a structure's fields. Theorem
proof bodies and proofs of structure-field obligations are checked by the
kernels and are optional reading for this review.

| Result | Definition/instance entries in its reading list | Additional existence statements |
| --- | ---: | --- |
| Theorem 3.1 | 112 | `exists_continuousMap` |
| Proposition 3.3 | 65 | None |
| Theorem 4.4 | 85 | None |
| Theorem 4.5 | 95 | None |
| Proposition 4.7 | 64 | None |

These lists overlap: the five main results together use **167 distinct listed
definitions/instances and one existence statement**. A shared definition needs
one review. The counts describe the reading lists, not a number of proofs to
check or an irreducible number of mathematical facts to learn.

Rows without the selected result's number are **optional for that result**.
The [additional paper claims](#additional-paper-claims) are optional when
reviewing only the five main results. Their statements and defining dependencies
become required when reviewing the corresponding appendix, architecture or
other paper claim. For example, Theorems 4.4–4.5 assume A1/A2; verifying that a
specific neural architecture satisfies A1/A2 is a separate claim.

This division assumes the [recorded proof verification](#proof-verification)
and standard Lean/Mathlib definitions are accepted. The vendored Tau Ceti
definitions are included in the required list for Theorem 3.1. Proof-only helper
lemmas, tactic implementations and performance logs are optional reading.

## Statements and definitions

Start with the challenge statement for each result under review:

| Result | Statement | Definition index |
| --- | --- | --- |
| Theorem 3.1 | [Homogenization](Comparator/Challenges/Homogenization.lean) | [Shared spaces](#tensor-and-periodic-spaces), [cell operators](#cell-operators-and-memory), [PDE definitions](#homogenization-and-function-spaces), [Sobolev background](#vendored-sobolev-background) |
| Proposition 3.3 | [Spectral representation](Comparator/Challenges/SpectralRepresentation.lean) | [Shared spaces](#tensor-and-periodic-spaces), [cell operators](#cell-operators-and-memory), [spectral measures](#spectral-measures) |
| Theorems 4.4–4.5 | [Approximation and dimension](Comparator/Challenges/UniversalApproximation.lean) | [Shared spaces](#tensor-and-periodic-spaces), [cell operators](#cell-operators-and-memory), [materials](#material-classes), [responses and dimension](#response-approximation-and-dimension) |
| Proposition 4.7 | [Spectral-edge discontinuity](Comparator/Challenges/SpectralEdge.lean) | [Shared spaces](#tensor-and-periodic-spaces), [cell operators](#cell-operators-and-memory), [materials](#material-classes), [strip example](#spectral-edge-example) |

For the appendix results and other paper claims, use `alignment.statements` in
[formalization.yaml](formalization.yaml) to locate their declarations and
challenge files. Whole-paper correspondence includes each of those claims;
some are split across several declarations.

The statement review covers:

- All hypotheses and quantifiers, including section-level `variable` and
  `include` declarations, implicit parameters and type-class assumptions.
- The definitions that give the statement its meaning, followed through their
  dependencies to familiar mathematical notions. This includes structure
  fields, notation, coercions and instances defining norms or topologies.
- Agreement with the paper's assumptions, conclusions, constants, dimensions,
  time domains and convergence notions, including the
  [mathematical qualifications](PLAN.md#mathematical-qualifications).

For example, reviewing `UniformlyApproximates` includes its material and strain
classes, `CellFamily`, `IsResponseSolution` and stress-error norm. Theorems
4.4–4.5 assume A1/A2; claims that a particular architecture satisfies A1/A2 have
their own entries in the correspondence record.

The numbering refers to the manuscript used for the recorded verification.
The final paper will be added to `paper/`; its correspondence with these
statements must be checked when it is added.

## Definition index

The index covers the five main results and the additional paper claims in
`alignment.statements`. It lists the project definitions used by those statements,
followed through their definition dependencies, and the relevant norm and
inner-product instances. Structure fields are part of the linked definition.

The **Required for** column identifies the main statements whose defining
dependencies include each group. For one theorem, read the rows bearing its
number. Shared definitions need one review. The later tables add definitions
for appendix, coordinate and architecture claims.

Lean and Mathlib supply the standard mathematical background: logic, real and
complex numbers, finite-dimensional Euclidean spaces, Lᵖ spaces, integrals,
continuous linear maps, topology and spectra. The index stops at these library
definitions. The vendored Sobolev constructions are listed separately below
because they supply additional mathematical definitions.

### Tensor and periodic spaces

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [SecondOrder](KVApproximation/Tensor/Spaces.lean#L20), [symmetricSubmodule](KVApproximation/Tensor/Spaces.lean#L24), [Symmetric](KVApproximation/Tensor/Spaces.lean#L38), [FourthOrder](KVApproximation/Tensor/Spaces.lean#L42), [elasticitySubmodule](KVApproximation/Tensor/Spaces.lean#L47), [Elasticity](KVApproximation/Tensor/Spaces.lean#L68) | Tensor spaces and dimensions: symmetric second-order arrays, major/minor fourth-order symmetries and the inherited Frobenius norms. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [strainDimension](KVApproximation/Tensor/Spaces.lean#L71) | The scalar strain dimension d(d+1)/2. | 3.3, 4.5 |
| [PositiveDefinite](KVApproximation/Tensor/Action.lean#L30) | A strictly positive lower quadratic-form bound for every symmetric strain. | 3.1 |
| [action](KVApproximation/Tensor/Action.lean#L19) | Contraction over both final tensor indices, using every ordered physical index pair. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [symmetrize](KVApproximation/Tensor/Symmetrization.lean#L18), [symmetrizeL](KVApproximation/Tensor/Symmetrization.lean#L25) | The factor one-half in the symmetric part and its continuous-linear-map version. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [actionLinear](KVApproximation/Tensor/LinearAction.lean#L17), [actionL](KVApproximation/Tensor/LinearAction.lean#L33) | The linear and continuous bilinear versions of tensor contraction. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [rescalePeriodic](KVApproximation/Analysis/PeriodicCell.lean#L40) | Evaluation of the periodic field at x/ε, with the torus quotient supplying periodic extension. | 3.1 |
| [PeriodicCell](KVApproximation/Analysis/PeriodicCell.lean#L18), [cellMeasure](KVApproximation/Analysis/PeriodicCell.lean#L22), [toCell](KVApproximation/Analysis/PeriodicCell.lean#L31), [cellRepresentative](KVApproximation/Analysis/PeriodicCell.lean#L36) | The unit torus, its normalized measure, the Euclidean quotient map and the coordinate representative. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [StrainField](KVApproximation/Tensor/Fields.lean#L21), [CoefficientField](KVApproximation/Tensor/Fields.lean#L25), [fieldPairing](KVApproximation/Tensor/Fields.lean#L30), [HasFieldBounds](KVApproximation/Tensor/Fields.lean#L36), [CoerciveField](KVApproximation/Tensor/Fields.lean#L42) | L² strain fields, Lᵖ coefficient fields, the integrated energy pairing and the bounds bundled with a coercive field. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [multiplication](KVApproximation/Tensor/Multiplication.lean#L24), [boundedFieldForm](KVApproximation/Tensor/Multiplication.lean#L30) | Pointwise coefficient multiplication and its bounded bilinear form on periodic L² strains. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [PeriodicJet](KVApproximation/Analysis/PeriodicSobolev.lean#L29), [PeriodicJetField](KVApproximation/Analysis/PeriodicSobolev.lean#L33), [periodicGradient](KVApproximation/Analysis/PeriodicSobolev.lean#L37), [smoothPeriodicJets](KVApproximation/Analysis/PeriodicSobolev.lean#L45), [periodicH1Submodule](KVApproximation/Analysis/PeriodicSobolev.lean#L52), [PeriodicH1](KVApproximation/Analysis/PeriodicSobolev.lean#L56) | Periodic H¹ as the closure of smooth value-gradient pairs; value, gradient, symmetric gradient, mean and zero-mean subspace. The linked instances specify the inherited Hilbert structures. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [PeriodicH1 inner product](KVApproximation/Analysis/PeriodicSobolev.lean#L58), [PeriodicH1.valueL](KVApproximation/Analysis/PeriodicSobolev.lean#L66), [PeriodicH1.gradientL](KVApproximation/Analysis/PeriodicSobolev.lean#L72), [PeriodicH1.symmetricGradientL](KVApproximation/Analysis/PeriodicSobolev.lean#L78), [cellAverageL](KVApproximation/Analysis/PeriodicSobolev.lean#L84), [zeroMeanPeriodicSubmodule](KVApproximation/Analysis/PeriodicSobolev.lean#L91) | Periodic H¹ as the closure of smooth value-gradient pairs; value, gradient, symmetric gradient, mean and zero-mean subspace. The linked instances specify the inherited Hilbert structures. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [ZeroMeanPeriodicH1](KVApproximation/Analysis/PeriodicSobolev.lean#L96), [ZeroMeanPeriodicH1 inner product](KVApproximation/Analysis/PeriodicSobolev.lean#L98), [correctorGradientL](KVApproximation/Analysis/PeriodicSobolev.lean#L107) | Periodic H¹ as the closure of smooth value-gradient pairs; value, gradient, symmetric gradient, mean and zero-mean subspace. The linked instances specify the inherited Hilbert structures. | 3.1, 3.3, 4.4, 4.5, 4.7 |

### Cell operators and memory

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [constantStrainL](KVApproximation/Homogenization/CorrectorSpace.lean#L43) | Embedding a macroscopic strain as a constant L² cell field. | 3.1, 3.3, 4.4, 4.5 |
| [correctorSubspace](KVApproximation/Homogenization/CorrectorSpace.lean#L23), [corrector subtype inner product](KVApproximation/Homogenization/CorrectorSpace.lean#L26), [corrector norm](KVApproximation/Homogenization/CorrectorSpace.lean#L32), [corrector inner product](KVApproximation/Homogenization/CorrectorSpace.lean#L35) | The closure of the symmetric-gradient range and its inherited L² norm and inner product. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [CoerciveField.toForm](KVApproximation/OperatorTheory/FieldForm.lean#L19) | Conversion of a periodic coefficient field into a coercive bilinear form. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [CoerciveForm.projection](KVApproximation/OperatorTheory/CoerciveForm.lean#L54), [CoerciveForm.complement](KVApproximation/OperatorTheory/CoerciveForm.lean#L61), [mismatch](KVApproximation/OperatorTheory/CoerciveForm.lean#L72), [CoerciveForm.homogenizedForm](KVApproximation/OperatorTheory/CoerciveForm.lean#L77) | The weighted projection P, complement Id−P, viscous–elastic projection difference and compressed effective form. | 3.1, 3.3, 4.4, 4.5 |
| [CoerciveForm](KVApproximation/OperatorTheory/CoerciveForm.lean#L23), [CoerciveForm.restrict](KVApproximation/OperatorTheory/CoerciveForm.lean#L37), [CoerciveForm.riesz](KVApproximation/OperatorTheory/CoerciveForm.lean#L49), [relaxation](KVApproximation/OperatorTheory/CoerciveForm.lean#L67) | The symmetric coercive form, its restriction and Riesz equivalence, and the relative operator obtained by composing the viscous inverse with elasticity. | 3.1, 3.3, 4.4, 4.5, 4.7 |
| [effectiveForm](KVApproximation/Homogenization/StaticCellOperators.lean#L27) | Specialization of the effective form to periodic correctors and constant strains. | 3.1, 3.3, 4.4, 4.5 |
| [relaxationSemigroup](KVApproximation/OperatorTheory/MemoryKernel.lean#L19), [memoryForm](KVApproximation/OperatorTheory/MemoryKernel.lean#L25) | The semigroup exp(−tR) and compression of R exp(−tR) through the mismatch, using the viscous pairing. | 3.1, 3.3, 4.4, 4.5 |
| [cellMemoryForm](KVApproximation/Homogenization/CellOperators.lean#L30), [CellConstitutiveModel](KVApproximation/Homogenization/CellOperators.lean#L37) | The compressed cell memory form and the identities fixing every component of the effective tensors and kernel. | 3.1, 3.3, 4.4, 4.5 |
| [cellRelaxation](KVApproximation/Homogenization/CellOperators.lean#L20) | The relative viscous–elastic operator on the concrete corrector space. | 4.7 |

### Homogenization and function spaces

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [PhysicalSpace](KVApproximation/Analysis/VectorSobolev.lean#L20), [VectorH1](KVApproximation/Analysis/VectorSobolev.lean#L25), [smoothCompactJets](KVApproximation/Analysis/VectorSobolev.lean#L30), [zeroBoundarySubmodule](KVApproximation/Analysis/VectorSobolev.lean#L37), [ZeroBoundaryH1](KVApproximation/Analysis/VectorSobolev.lean#L42), [ZeroBoundaryH1 norm](KVApproximation/Analysis/VectorSobolev.lean#L46) | Euclidean physical space, componentwise H¹, closure of smooth compactly supported displacements, value/gradient representatives and the inherited H¹₀ norm and inner product. | 3.1 |
| [ZeroBoundaryH1 inner product](KVApproximation/Analysis/VectorSobolev.lean#L51), [VectorH1.value](KVApproximation/Analysis/VectorSobolev.lean#L60), [VectorH1.gradientEntry](KVApproximation/Analysis/VectorSobolev.lean#L66) | The inherited spatial Hilbert structure and the representatives of displacement values and full weak-gradient entries. | 3.1 |
| [dropCoordinate](KVApproximation/Analysis/LipschitzDomain.lean#L18), [HasLipschitzBoundary](KVApproximation/Analysis/LipschitzDomain.lean#L24) | The local graph definition of a Lipschitz boundary after translation and an orthogonal coordinate change. | 3.1 |
| [TimeH1](KVApproximation/Analysis/TimeSobolev.lean#L21), [TimeH1.value](KVApproximation/Analysis/TimeSobolev.lean#L27), [TimeH1.velocity](KVApproximation/Analysis/TimeSobolev.lean#L32), [TimeH1.trace](KVApproximation/Analysis/TimeSobolev.lean#L36), [TimeH1.initial](KVApproximation/Analysis/TimeSobolev.lean#L41) | H¹ time trajectories, inverse-Riesz identification of the weak derivative, continuous traces and evaluation at time zero. | 3.1 |
| [SpatialL2](KVApproximation/Homogenization/StaticWeakProblem.lean#L22), [symmetricGradient](KVApproximation/Homogenization/StaticWeakProblem.lean#L27), [spatialForm](KVApproximation/Homogenization/StaticWeakProblem.lean#L37), [loadPairing](KVApproximation/Homogenization/StaticWeakProblem.lean#L42), [IsPreparedInitialFamily](KVApproximation/Homogenization/StaticWeakProblem.lean#L48) | L² loads, the symmetric spatial gradient, elasticity bilinear form, load pairing and elastic preparation with a fixed load at every positive scale. | 3.1 |
| [Forcing](KVApproximation/Homogenization/WeakProblem.lean#L22), [IsMicroscopicSolution](KVApproximation/Homogenization/WeakProblem.lean#L27), [IsHomogenizedSolution](KVApproximation/Homogenization/WeakProblem.lean#L42) | L²-in-time forcing; initial conditions and weak microscopic/homogenized balances, with one almost-everywhere time condition for all spatial tests. | 3.1 |

### Spectral measures

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [TensorMeasure](KVApproximation/Spectral/TensorMeasure.lean#L22), [TensorMeasure.Positive](KVApproximation/Spectral/TensorMeasure.lean#L25), [TensorMeasure.SupportedOn](KVApproximation/Spectral/TensorMeasure.lean#L30), [tensorIntegral](KVApproximation/Spectral/TensorMeasure.lean#L35), [totalVariation](KVApproximation/Spectral/TensorMeasure.lean#L40) | Tensor-valued measures, positivity on Borel sets, support via variation, scalar integration and Frobenius total variation. | 3.3 |
| [lowerRate](KVApproximation/Spectral/Bounds.lean#L19), [upperRate](KVApproximation/Spectral/Bounds.lean#L23), [spectralVariationBound](KVApproximation/Spectral/Bounds.lean#L28) | The lower and upper relaxation rates and the quantitative spectral-variation bound. | 3.3 |

### Material classes

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [PeriodicC1](KVApproximation/Analysis/PeriodicSmooth.lean#L18), [PeriodicC1.partial](KVApproximation/Analysis/PeriodicSmooth.lean#L23) | Periodic C¹ test functions and coordinate derivatives used to define variation. | 4.4, 4.5, 4.7 |
| [PeriodicC1.divergence](KVApproximation/Analysis/PeriodicVariation.lean#L20), [periodicVariation](KVApproximation/Analysis/PeriodicVariation.lean#L27), [periodicBVNorm](KVApproximation/Analysis/PeriodicVariation.lean#L36) | Divergence of vector-valued tests, the dual total-variation seminorm and the L¹-plus-variation BV norm. | 4.4, 4.5, 4.7 |
| [Material](KVApproximation/KelvinVoigt/Material.lean#L21), [admissibleMaterials](KVApproximation/KelvinVoigt/Material.lean#L26) | The L² product topology on viscosity/elasticity pairs and the L∞, ellipticity and BV constraints defining admissible materials. | 4.4, 4.5, 4.7 |
| [CoerciveField.ofMemLp](KVApproximation/Tensor/MultiplicationIdentities.lean#L39) | Conversion of an Lᵖ representative with an L∞ witness into a CoerciveField, preserving its specified energy bounds. | 4.4, 4.5, 4.7 |
| [materialViscosity](KVApproximation/KelvinVoigt/MaterialFields.lean#L20), [materialElasticity](KVApproximation/KelvinVoigt/MaterialFields.lean#L25) | Extraction of viscosity and elasticity from an admissible material, with their respective bounds. | 4.4, 4.5, 4.7 |

### Response approximation and dimension

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [timeMeasure](KVApproximation/Dynamics/Trajectory.lean#L23), [BoundedTrajectory](KVApproximation/Dynamics/Trajectory.lean#L28), [BoundedTrajectory.valueBound](KVApproximation/Dynamics/Trajectory.lean#L40), [BoundedTrajectory.velocityBound](KVApproximation/Dynamics/Trajectory.lean#L45), [BoundedTrajectory.Admissible](KVApproximation/Dynamics/Trajectory.lean#L50), [BoundedTrajectory.Agree](KVApproximation/Dynamics/Trajectory.lean#L56) | Half-line measure; bounded value/velocity representatives with their integral identity; strain admissibility, trajectory equality and the zero-initial kinetic equation. | 4.4, 4.5 |
| [IsKineticSolution](KVApproximation/Dynamics/Trajectory.lean#L62) | Zero initial internal state and the kinetic ODE almost everywhere on the nonnegative time axis. | 4.4, 4.5 |
| [HasUniversalApproximation](KVApproximation/NeuralOperators/Classes.lean#L23), [HasLocallyLipschitzApproximation](KVApproximation/NeuralOperators/Classes.lean#L31) | A1/A2: quantifier order, compact input sets, continuous target maps, uniform error and local Lipschitz dependence for the same approximator. | 4.4, 4.5 |
| [StressInput](KVApproximation/NeuralOperators/ResponseModel.lean#L21), [KineticInput](KVApproximation/NeuralOperators/ResponseModel.lean#L24), [stressAlong](KVApproximation/NeuralOperators/ResponseModel.lean#L33), [IsResponseSolution](KVApproximation/NeuralOperators/ResponseModel.lean#L39) | Euclidean stress/kinetic input products, evaluation of stress along trajectories and the response ODE. | 4.4, 4.5 |
| [CellFamily](KVApproximation/KelvinVoigt/Constitutive.lean#L21), [constitutiveStress](KVApproximation/KelvinVoigt/Constitutive.lean#L28) | The cell model for each material and the constitutive stress, including its memory convolution. | 4.4, 4.5 |
| [InternalState](KVApproximation/KelvinVoigt/ApproximationProblem.lean#L21), [StressResponseClass](KVApproximation/KelvinVoigt/ApproximationProblem.lean#L25), [KineticResponseClass](KVApproximation/KelvinVoigt/ApproximationProblem.lean#L29), [UniformlyApproximates](KVApproximation/KelvinVoigt/ApproximationProblem.lean#L35) | Scalar internal states and response classes; uniform approximation, including existence/uniqueness of the trajectory and its half-line essential-supremum stress error. | 4.4, 4.5 |
| [sufficientDimension](KVApproximation/KelvinVoigt/ApproximationProblem.lean#L52) | The scalar state count, with a separate singleton-spectrum branch. | 4.5 |
| [ellipseResponseFactor](KVApproximation/Approximation/Constants.lean#L25), [pronyConstant](KVApproximation/Approximation/Constants.lean#L40) | The ellipse-response factor and Prony constant entering the dimension bound. | 4.5 |
| [log2Positive](KVApproximation/Approximation/Dimension.lean#L18), [interpolationOrder](KVApproximation/Approximation/Dimension.lean#L23), [logPartitionIntervals](KVApproximation/Approximation/Dimension.lean#L28), [logPartitionCount](KVApproximation/Approximation/Dimension.lean#L33), [nonsingletonStateDimension](KVApproximation/Approximation/Dimension.lean#L44) | Positive-part logarithm, ceiling conventions, interpolation order, logarithmic partition count and scalar state count. | 4.5 |
| [logarithmicSpan](KVApproximation/Approximation/LogPartition.lean#L17) | The logarithmic spectral span. | 4.5 |

### Spectral-edge example

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [delta](KVApproximation/Tensor/Isotropic.lean#L16), [identityElasticity](KVApproximation/Tensor/Isotropic.lean#L28) | Kronecker delta and the identity operator on symmetric strains, including the symmetrization factor. | 4.7 |
| [thinStrip](KVApproximation/KelvinVoigt/StripFields.lean#L20), [stripElasticity](KVApproximation/KelvinVoigt/StripFields.lean#L25) | The strip width 1/(m+1), its coordinate condition and the piecewise elasticity values one and two. | 4.7 |
| [upperSpectralEdge](KVApproximation/OperatorTheory/Spectrum.lean#L19) | The supremum of the full real operator spectrum. | 4.7 |
| [upperSpectralEdge](KVApproximation/KelvinVoigt/SpectralEdge.lean#L23), [materialSpectralEdge](KVApproximation/KelvinVoigt/SpectralEdge.lean#L28) | Specialization of that spectral edge to cell relaxation and then to the admissible material class. | 4.7 |

### Vendored Sobolev background

These definitions are from Tau Ceti, with attribution in
[Vendor/NOTICE.md](Vendor/NOTICE.md). They underlie Theorem 3.1’s spatial
and time Sobolev spaces. Read the data, membership predicates, component
maps and trace choice; the proofs of their properties are kernel-checked.

| Definitions | Meaning to check | Required for |
| --- | --- | --- |
| [testFunctionLp](Vendor/TauCeti/Analysis/Sobolev/TestFunctionLp.lean#L51) | Conversion of smooth compactly supported test functions into Lᵖ classes. | 3.1 |
| [WeakDerivStepJetLp](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L69), [weakDerivStepBaseL](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L77), [weakDerivStepDirectionL](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L89), [weakDerivStepSmulPairing](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L101), [weakDerivStepTestFunctional](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L111), [weakDerivStepSubmodule](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L161) | The value/derivative graph, its test functionals and integration-by-parts constraints, and the projections to its two components. | 3.1 |
| [WeakDerivStep](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L206), [prevL](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L213), [weakFDerivL](Vendor/TauCeti/Analysis/Sobolev/GraphStep.lean#L231) | The closed weak-derivative space and its value/derivative projections. | 3.1 |
| [Sobolev1Jet](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L103), [Sobolev1JetLp](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L107), [Sobolev1JetLp.valueL](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L132), [Sobolev1JetLp.gradientL](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L151), [toWeakDerivStepJet](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L291), [w1pSubmodule](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L321) | Scalar Sobolev jets, their value/gradient projections and the closed weak-derivative graph defining W¹,ᵖ. | 3.1 |
| [W1p](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L366), [W1p.valueL](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L374), [W1p.value](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L378), [W1p.gradientL](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L385), [W1p.gradient](Vendor/TauCeti/Analysis/Sobolev/W1p/Basic.lean#L389) | The scalar Sobolev subtype and the maps extracting its Lᵖ value and weak gradient. | 3.1 |
| [gelfandDual](Vendor/TauCeti/Analysis/InnerProductSpace/GelfandTriple.lean#L59) | The pivot-space map to the continuous dual used in the time-derivative definition. | 3.1 |
| [ContinuousLinearMap.evolutionBaseL](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L56), [EvolutionSpace](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L73), [valueL](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L81), [timeDerivL](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L86), [value](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L94), [timeDeriv](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L97) | The L² value/dual-derivative graph, its projections and the choice of continuous representative used for endpoint traces. | 3.1 |
| [representativeₗ](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L301), [toContinuousMap](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L344) | Selection of the continuous time representative and its packaging as a bounded linear trace map. | 3.1 |

### Definitions using existence results

A definition using `.choose` selects an object supplied by an existence theorem.
The following theorem statements specify the selected objects. Read a statement
when reviewing a result in its **Required when reviewing** column. Only
`exists_continuousMap` is needed for the five main results, specifically Theorem
3.1. The other five statements belong to the additional paper claims. All six
proof bodies are covered by kernel verification.

| Statement | Meaning to check | Required when reviewing |
| --- | --- | --- |
| [exists_continuousMap](Vendor/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L274) | The continuous representative chosen for the time trace agrees almost everywhere with the trajectory values. | 3.1; Remark 3.2; Appendix A |
| [lp_finite_coordinates](KVApproximation/Analysis/LpFiniteCoordinates.lean#L22) | The coordinate isometry used to assemble componentwise spatial gradients. | Remark 1.2 |
| [lp_coordinates](KVApproximation/Analysis/LpCoordinates.lean#L19) | Pointwise transport of Lᵖ fields through a linear isometry, including representative agreement. | Remark 1.2; B.12 |
| [lp_product_coordinates](KVApproximation/Analysis/LpProductCoordinates.lean#L19) | The continuous linear equivalence between a pair of L² fields and one product-valued L² field. | B.12 |
| [scalarStrainMandel_isometry](KVApproximation/Tensor/MandelFiniteIsometry.lean#L16) | The strain isometry whose coordinates equal scalarStrainMandel. | B.12 |
| [scalarElasticityMandel_isometry](KVApproximation/Tensor/MandelFiniteIsometry.lean#L27) | The elasticity isometry whose coordinates equal scalarElasticityMandel. | B.12 |

### Additional paper claims

These tables extend the preceding lists for the statements identified in
[formalization.yaml](formalization.yaml). They include definitions given directly
in the paper, such as the Prony construction and the crystal-plasticity laws,
even when a definition is not mentioned in a main theorem.

**Optional for the five main results; required for the corresponding additional
claim.** Use the claim's entry in `alignment.statements` to select its declarations
and follow their definitions. These tables are a combined index for those claims,
not a requirement to read every entry for each appendix result.

#### Additional analysis and cell definitions

| Definitions | Meaning to check |
| --- | --- |
| [HasPeriodicDistributionalGradient](KVApproximation/Analysis/PeriodicDistributionalGradient.lean#L20) | The periodic distributional-gradient identity and its integrability hypotheses (Remark 4.1). |
| [gradientRowCoordinates](KVApproximation/Analysis/VectorSobolevFields.lean#L23), [VectorH1.gradientL](KVApproximation/Analysis/VectorSobolevFields.lean#L54), [VectorH1.symmetricGradientL](KVApproximation/Analysis/VectorSobolevFields.lean#L69) | Physical gradient-row coordinates and the L² full/symmetric-gradient maps. |
| [cellMismatch](KVApproximation/Homogenization/CellOperators.lean#L25) | The cell projection mismatch used in the appendix evolution. |
| [cellProjection](KVApproximation/Homogenization/StaticCellOperators.lean#L21) | The coefficient-weighted cell projection. |
| [IsDisplacementStrain](KVApproximation/Homogenization/CorrectorTrajectory.lean#L22) | Identification of a displacement trajectory with its strain-corrector trajectory. |
| [periodicCellStress](KVApproximation/Homogenization/CellDisplacement.lean#L23), [IsPeriodicCellSolution](KVApproximation/Homogenization/CellDisplacement.lean#L37), [averagedCellStress](KVApproximation/Homogenization/CellDisplacement.lean#L51) | The periodic weak cell equation, pointwise cell stress and its spatial average. |
| [IsCellEvolution](KVApproximation/Dynamics/CellEvolution.lean#L25), [cellStressPairing](KVApproximation/Dynamics/CellEvolution.lean#L35) | The corrector-space ODE and its tested stress pairing. |
| [rescaledCoefficient](KVApproximation/Homogenization/RescaledFields.lean#L21) | Rescaled coefficients as L∞ fields on the physical domain. |
| [boundedSpatialForm](KVApproximation/Homogenization/SpatialOperators.lean#L34) | The bounded spatial form built from L² strain multiplication. |
| [periodicSpatialForm](KVApproximation/Homogenization/SpatialEvolutionOperators.lean#L24), [microscopicRelaxation](KVApproximation/Homogenization/SpatialEvolutionOperators.lean#L34) | The spatial coercive form and microscopic relaxation operator (Remark 1.2). |
| [CoerciveForm.HasBounds](KVApproximation/OperatorTheory/CoerciveForm.lean#L32) | Quantitative lower and upper energy bounds on a coercive form. |
| [relativeRiesz](KVApproximation/OperatorTheory/CoerciveSolvers.lean#L25) | The relative Riesz operator used for spatial relaxation. |
| [HasBounds](KVApproximation/Tensor/Action.lean#L35) | Pointwise quadratic-form lower and upper bounds. |
| [IsSpectralRepresentation](KVApproximation/Spectral/TensorMeasure.lean#L45), [resolventWeight](KVApproximation/Spectral/TensorMeasure.lean#L52), [weightedMeasure](KVApproximation/Spectral/TensorMeasure.lean#L57) | The spectral-representation predicate, resolvent weight and weighted vector measure (B.5–B.6). |
| [weightedVariationBound](KVApproximation/Spectral/Bounds.lean#L34) | The weighted spectral-variation constant (B.6). |

#### Chebyshev and Prony definitions

| Definitions | Meaning to check |
| --- | --- |
| [weightedResponse](KVApproximation/Approximation/WeightedResponse.lean#L26) | The complex weighted response as a finite-time exponential convolution (B.7). |
| [bernsteinImaginarySemiaxis](KVApproximation/Approximation/Constants.lean#L20), [chebyshevErrorBound](KVApproximation/Approximation/Constants.lean#L30), [localResponseErrorBound](KVApproximation/Approximation/Constants.lean#L35), [pronyErrorBound](KVApproximation/Approximation/Constants.lean#L45) | Ellipse geometry and Chebyshev/local-response/Prony error constants. |
| [logPartitionWidth](KVApproximation/Approximation/Dimension.lean#L38) | The logarithmic partition width. |
| [logPartitionCenter](KVApproximation/Approximation/LogPartition.lean#L21), [logPatchLeft](KVApproximation/Approximation/LogPartition.lean#L25), [logPatchRight](KVApproximation/Approximation/LogPartition.lean#L29), [logHat](KVApproximation/Approximation/LogPartition.lean#L33), [spectralWeight](KVApproximation/Approximation/LogPartition.lean#L37), [localRate](KVApproximation/Approximation/LogPartition.lean#L43) | Partition centers, hat functions, patch endpoints, spectral weights and local spectral coordinates/rates (B.8). |
| [localCoordinate](KVApproximation/Approximation/LogPartition.lean#L49) | The inverse local spectral coordinate. |
| [bernsteinEllipse](KVApproximation/Approximation/Interpolation.lean#L19), [chebyshevNode](KVApproximation/Approximation/Interpolation.lean#L25), [chebyshevLagrange](KVApproximation/Approximation/Interpolation.lean#L29), [chebyshevInterpolant](KVApproximation/Approximation/Interpolation.lean#L34) | Chebyshev nodes, Lagrange factors, the interpolant and the Bernstein ellipse (B.8–B.9). |
| [complexLocalRate](KVApproximation/Approximation/LocalResponse.lean#L20), [localWeightedResponse](KVApproximation/Approximation/LocalResponse.lean#L25) | The complex local rate and the weighted response in local coordinates. |
| [localPronyRate](KVApproximation/Approximation/LogProny.lean#L21), [localPronyCoefficient](KVApproximation/Approximation/LogProny.lean#L28), [singletonPronyCoefficient](KVApproximation/Approximation/LogProny.lean#L38), [localPronyKernel](KVApproximation/Approximation/LogProny.lean#L43) | Signed local coefficient integrals, rates, assembled kernel and the singleton coefficient. |
| [localPronyModel](KVApproximation/Approximation/PronyModels.lean#L21), [singletonPronyModel](KVApproximation/Approximation/PronyModels.lean#L37) | The local and singleton Prony models assembled from these quantities. |
| [BlockState](KVApproximation/Dynamics/PronyModel.lean#L20), [PronyModel](KVApproximation/Dynamics/PronyModel.lean#L26), [PronyModel.kernel](KVApproximation/Dynamics/PronyModel.lean#L35), [PronyModel.stressResponse](KVApproximation/Dynamics/PronyModel.lean#L39), [PronyModel.kineticResponse](KVApproximation/Dynamics/PronyModel.lean#L44), [PronyModel.state](KVApproximation/Dynamics/PronyModel.lean#L52) | Euclidean block states, model coefficients/rates, kernel, internal trajectory, stress and response maps (B.10–B.13). |
| [PronyModel.stress](KVApproximation/Dynamics/PronyModel.lean#L59) | Stress assembled from viscosity, elasticity, strain/velocity and the signed internal-state contributions. |
| [SpectralFamily](KVApproximation/KelvinVoigt/PronyProblem.lean#L22), [uniformPronyError](KVApproximation/KelvinVoigt/PronyProblem.lean#L31) | The material-dependent spectral family and the uniform material/strain/time error. |
| [unweightedLocalCoefficient](KVApproximation/Approximation/AlternativeProny.lean#L20), [unweightedLocalModel](KVApproximation/Approximation/AlternativeProny.lean#L27), [globalLogRate](KVApproximation/Approximation/AlternativeProny.lean#L41), [globalLogCoordinate](KVApproximation/Approximation/AlternativeProny.lean#L45), [globalPronyCoefficient](KVApproximation/Approximation/AlternativeProny.lean#L49), [globalPronyModel](KVApproximation/Approximation/AlternativeProny.lean#L56) | Global weighted and unweighted Prony coefficients, rates and kernels (Remark 4.6). |
| [unweightedErrorConstant](KVApproximation/Approximation/AlternativeDimension.lean#L17), [unweightedDimension](KVApproximation/Approximation/AlternativeDimension.lean#L22), [globalPronyErrorBound](KVApproximation/Approximation/AlternativeDimension.lean#L28), [globalInterpolationOrder](KVApproximation/Approximation/AlternativeDimension.lean#L32), [globalPronyDimension](KVApproximation/Approximation/AlternativeDimension.lean#L37) | Alternative error constants, interpolation order and dimension formulas (Remark 4.6 and the dimension asymptotics). |

#### Coordinates and neural architectures

| Definitions | Meaning to check |
| --- | --- |
| [elasticityDimension](KVApproximation/Tensor/Spaces.lean#L74) | The dimension of the elasticity-tensor space. |
| [appendEuclidean](KVApproximation/Analysis/EuclideanCoordinates.lean#L18) | Concatenation of Euclidean coordinate blocks. |
| [StrainIndex](KVApproximation/Tensor/MandelCoordinates.lean#L17), [mandelWeight](KVApproximation/Tensor/MandelCoordinates.lean#L20), [strainMandel](KVApproximation/Tensor/MandelCoordinates.lean#L25), [strainIndexCode](KVApproximation/Tensor/MandelCoordinates.lean#L29), [ElasticityIndex](KVApproximation/Tensor/MandelCoordinates.lean#L32), [elasticityMandel](KVApproximation/Tensor/MandelCoordinates.lean#L38) | Independent strain/elasticity indices, off-diagonal weights and Mandel coordinate maps. |
| [blockStrainMandel](KVApproximation/Tensor/MandelBlocks.lean#L17) | Mandel coordinates for tensor-valued internal-state blocks. |
| [strainIndexEquivFin](KVApproximation/Tensor/MandelFiniteIndices.lean#L19), [elasticityIndexEquivFin](KVApproximation/Tensor/MandelFiniteIndices.lean#L24), [scalarStrainMandel](KVApproximation/Tensor/MandelFiniteIndices.lean#L29), [scalarElasticityMandel](KVApproximation/Tensor/MandelFiniteIndices.lean#L35), [blockMandelIndexEquiv](KVApproximation/Tensor/MandelFiniteIndices.lean#L41), [scalarBlockStrainMandel](KVApproximation/Tensor/MandelFiniteIndices.lean#L47) | Finite index orderings and scalar strain, elasticity and internal-state coordinates. |
| [inducedResponse](KVApproximation/NeuralOperators/CoordinateClasses.lean#L26), [inducedResponseClass](KVApproximation/NeuralOperators/CoordinateClasses.lean#L34) | Transport of response maps and approximation classes through input/output/material coordinates. |
| [stressStateCoordinates](KVApproximation/NeuralOperators/StateCoordinates.lean#L24), [kineticStateCoordinates](KVApproximation/NeuralOperators/StateCoordinates.lean#L31), [coordinateStressResponse](KVApproximation/NeuralOperators/StateCoordinates.lean#L37), [coordinateKineticResponse](KVApproximation/NeuralOperators/StateCoordinates.lean#L43) | Transport of stress/kinetic inputs and response maps through internal-state coordinates. |
| [stressInputSet](KVApproximation/NeuralOperators/PronyResponses.lean#L23), [kineticInputSet](KVApproximation/NeuralOperators/PronyResponses.lean#L29), [pronyStressResponse](KVApproximation/NeuralOperators/PronyResponses.lean#L33), [pronyKineticResponse](KVApproximation/NeuralOperators/PronyResponses.lean#L39) | Compact response input sets and Prony stress/kinetic targets (B.11–B.12). |
| [strainMandelEquiv](KVApproximation/KelvinVoigt/MandelResponses.lean#L25), [elasticityMandelEquiv](KVApproximation/KelvinVoigt/MandelResponses.lean#L30), [ScalarMaterial](KVApproximation/KelvinVoigt/MandelResponses.lean#L36), [materialValueCoordinates](KVApproximation/KelvinVoigt/MandelResponses.lean#L41), [materialMandelCoordinates](KVApproximation/KelvinVoigt/MandelResponses.lean#L50), [kineticMandelCoordinates](KVApproximation/KelvinVoigt/MandelResponses.lean#L59) | Scalar material encoding, material topology and Mandel stress/kinetic response classes. |
| [stressMandelCoordinates](KVApproximation/KelvinVoigt/MandelResponses.lean#L68), [mandelStressClass](KVApproximation/KelvinVoigt/MandelResponses.lean#L78), [mandelKineticClass](KVApproximation/KelvinVoigt/MandelResponses.lean#L86) | Mandel stress-input coordinates and the transported scalar-network response classes. |
| [Feedforward](KVApproximation/NeuralOperators/Feedforward.lean#L20), [Feedforward.eval](KVApproximation/NeuralOperators/Feedforward.lean#L29) | Finite feedforward-network constructors and their evaluation. |
| [Channels](KVApproximation/NeuralOperators/FourierMapping.lean#L24), [ChannelField](KVApproximation/NeuralOperators/FourierMapping.lean#L27), [frequencyBox](KVApproximation/NeuralOperators/FourierMapping.lean#L30), [channelFourier](KVApproximation/NeuralOperators/FourierMapping.lean#L34), [FourierLayer](KVApproximation/NeuralOperators/FourierMapping.lean#L40), [FourierLayer.fourierPart](KVApproximation/NeuralOperators/FourierMapping.lean#L50) | Channel fields, Fourier coefficients/projections, layers, composition, lifting/output and the represented class (Example 2.1 and Remark 4.3). |
| [FourierLayer.eval](KVApproximation/NeuralOperators/FourierMapping.lean#L56), [FourierChain](KVApproximation/NeuralOperators/FourierMapping.lean#L62), [FourierChain.eval](KVApproximation/NeuralOperators/FourierMapping.lean#L68), [FourierProjection](KVApproximation/NeuralOperators/FourierMapping.lean#L75), [FourierProjection.complexValue](KVApproximation/NeuralOperators/FourierMapping.lean#L82), [FourierProjection.eval](KVApproximation/NeuralOperators/FourierMapping.lean#L89) | Layer evaluation, composition and the final Fourier projection, including complex evaluation and real extraction. |
| [FourierMapping](KVApproximation/NeuralOperators/FourierMapping.lean#L95), [FourierMapping.evalRepresentative](KVApproximation/NeuralOperators/FourierMapping.lean#L105), [FourierMapping.eval](KVApproximation/NeuralOperators/FourierMapping.lean#L112), [fourierMappingClass](KVApproximation/NeuralOperators/FourierMapping.lean#L119) | The lifting/chain/output architecture, evaluation on representatives and the class of continuous maps represented by it. |
| [FeedforwardFourierMapping](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L20), [FeedforwardFourierMapping.hiddenRepresentative](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L30), [FeedforwardFourierMapping.evalRepresentative](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L38), [FeedforwardFourierMapping.eval](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L45), [feedforwardFourierMappingClass](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L53), [FourierMapping.toFeedforward](KVApproximation/NeuralOperators/FeedforwardFourierMapping.lean#L61) | Feedforward lifting/output around a Fourier chain, representative evaluation and the resulting architecture class. |
| [ActivatedFourierChain](KVApproximation/NeuralOperators/ActivatedFourierChain.lean#L19), [ActivatedFourierChain.eval](KVApproximation/NeuralOperators/ActivatedFourierChain.lean#L26), [ActivatedFourierChain.HasLipschitzActivations](KVApproximation/NeuralOperators/ActivatedFourierChain.lean#L34), [FourierChain.withActivation](KVApproximation/NeuralOperators/ActivatedFourierChain.lean#L41) | Layer-dependent activations, their Lipschitz condition, evaluation and the embedding of a shared-activation chain. |

#### Numerical-appendix definitions

| Definitions | Meaning to check |
| --- | --- |
| [identityStrain](KVApproximation/Tensor/Isotropic.lean#L23), [volumetricElasticity](KVApproximation/Tensor/Isotropic.lean#L45), [planeStress](KVApproximation/Tensor/Isotropic.lean#L55) | Identity strain, isotropic volumetric tensor and plane-stress reduction (Appendix C). |
| [blockInsertion](KVApproximation/Examples/LinearSurrogate.lean#L20), [inputBlock](KVApproximation/Examples/LinearSurrogate.lean#L24), [evolutionBlock](KVApproximation/Examples/LinearSurrogate.lean#L28) | Internal-state block insertion and transformed input/evolution blocks after the stated coordinate change (Appendix C). |
| [Mat3](KVApproximation/Examples/CrystalPlasticity.lean#L19), [greenStrain](KVApproximation/Examples/CrystalPlasticity.lean#L22), [cubicStress](KVApproximation/Examples/CrystalPlasticity.lean#L26), [copperStress](KVApproximation/Examples/CrystalPlasticity.lean#L31), [firstPiola](KVApproximation/Examples/CrystalPlasticity.lean#L35), [resolvedShear](KVApproximation/Examples/CrystalPlasticity.lean#L39) | Three-dimensional matrices; Green strain, cubic and copper stiffness, first Piola stress and resolved-shear contraction. |
| [slipRate](KVApproximation/Examples/CrystalPlasticity.lean#L43), [copperSlipRate](KVApproximation/Examples/CrystalPlasticity.lean#L47), [fccInteractionWeights](KVApproximation/Examples/CrystalPlasticity.lean#L52), [plasticVelocity](KVApproximation/Examples/CrystalPlasticity.lean#L56), [plasticRate](KVApproximation/Examples/CrystalPlasticity.lean#L60), [hardeningRate](KVApproximation/Examples/CrystalPlasticity.lean#L65) | Slip-rate and hardening formulas, copper slip parameters, the seven interaction weights and plastic-distortion evolution. |
| [copperHardeningRate](KVApproximation/Examples/CrystalPlasticity.lean#L71), [copperGrainParameters](KVApproximation/Examples/CrystalPlasticity.lean#L77), [skew](KVApproximation/Examples/CrystalPlasticity.lean#L83), [rotation](KVApproximation/Examples/CrystalPlasticity.lean#L87), [logarithmicStrain](KVApproximation/Examples/CrystalPlasticity.lean#L90), [deviatoricFromCoordinates](KVApproximation/Examples/CrystalPlasticity.lean#L95) | Copper hardening parameters and units; skew/rotation matrices, logarithmic strain and the explicit trace-free basis. |
| [deviatoricCoordinates](KVApproximation/Examples/CrystalPlasticity.lean#L99), [deformation](KVApproximation/Examples/CrystalPlasticity.lean#L104) | Inverse deviatoric coordinates and the rotation/stretch reconstruction of the deformation gradient. |

## Proof verification

Comparator matches each selected solution theorem to its challenge statement
and checks the exported proofs. The `sorry` bodies in the separate challenge
files designate statements to prove. Accepted solution proofs may depend only
on `propext`, `Quot.sound` and `Classical.choice`.

The existing verification evidence is:

- [Combined coverage](Verification/results/vm/combined/coverage.json):
  `passed: true`, 331/331 configurations and 702 selected declarations, with
  every configuration accepted by all six kernels.
- [Transitive axiom audit](Verification/results/vm/axioms.json):
  `passed: true`, covering every selected declaration and reporting only the
  three axioms above.

Theorem proof bodies can be skipped during this review: the kernels check the
proof terms and their dependencies. The mathematical review concerns the meaning
and coverage of the statements. This relies on Lean's logic and the verification
toolchain, as described in the [Lean reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Saved results apply to the sources used in their run. Changes to statements,
definitions or proofs require the affected checks to be rerun using the
[verification commands](README.md#verification).
