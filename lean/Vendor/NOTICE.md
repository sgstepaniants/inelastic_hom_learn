# Third-party source

The selected sources in `TauCeti/` come from [Tau Ceti](https://github.com/TauCetiProject/TauCeti), from its Lean 4.35 development before the October 2026 toolchain update. Copyright © 2026 The Tau Ceti contributors. Apache-2.0.

The Fréchet–Kolmogorov closure consists of `MeasureTheory/Function/Lp/FrechetKolmogorov.lean`, `MeasureTheory/Function/Lp/BallAverage.lean`, and `Topology/ContinuousMap/Ascoli.lean`, from the upstream `v4.35.0` tag.

The Dirichlet Poincaré closure, `Analysis/Sobolev/W1p/Zero.lean`, `Analysis/Sobolev/Poincare/Slab.lean` and `Analysis/Sobolev/Poincare/W1p0.lean`, comes from the upstream `v4.35.0` tag.

The Dirichlet Rellich–Kondrachov closure also comes from `v4.35.0`: `Analysis/Sobolev/RellichKondrachov.lean`, `Analysis/Sobolev/Translation.lean`, `Analysis/Sobolev/W1p/Extension.lean`, `Analysis/Distribution/TestFunction/Translation.lean`, `MeasureTheory/Function/Lp/ExtendByZero.lean` and `MeasureTheory/Function/Lp/CastMeasure.lean`. It uses the zero-boundary Sobolev and Fréchet–Kolmogorov sources listed above.

The compact-parameter integration closure, `Analysis/Calculus/ParametricIntegral.lean` and `Topology/Compactness/Normed.lean`, also comes from `v4.35.0`. Only the closed-unit-interval results needed here are retained from the former file.

`KVApproximation/Analysis/PrimitiveIntegrationByParts.lean` adapts the Fubini proof in Tau Ceti's `MeasureTheory/Integral/IntervalIntegral/Primitive.lean` to real or complex scalar functions, retaining its copyright and Apache-2.0 notice.

`KVApproximation/Dynamics/Caratheodory.lean` adapts the Picard construction in Tau Ceti's [`Analysis/ODE/Caratheodory.lean`](https://github.com/TauCetiProject/TauCeti/blob/v4.35.0/TauCeti/Analysis/ODE/Caratheodory.lean) to nonlinear fields with a uniform state Lipschitz bound, retaining its copyright and Apache-2.0 notice.

The sources in `ForTauCeti/` come from [AIQ–Kitware's Davis–Kahan formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization), from its Lean 4.34 release-candidate development. Copyright © 2026 Kitware, Inc. Authors: Jon Crall and Claude Opus 5. Apache-2.0.

`BorelCalculus/Polarization.lean` supplies an explicit measurability hypothesis required by Mathlib 4.35's L¹ norm identity.

`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean` includes code adapted from [Spectra](https://github.com/adambornemann-glitch/Spectra). Copyright © 2026 Spectra Formalization Project. Author: Adam Bornemann. Apache-2.0. The upstream adaptation changes the namespace to `TauCeti`; its local module documentation has been shortened.

The original copyright and license notices are retained in each source. The license text is in [LICENSE](../LICENSE).

Tau Ceti's `Analysis/Calculus/SegmentIncrement.lean` adapts a result from [DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi), by Scott Armstrong and Julia Kempe, under Apache-2.0. Its local source citation has been shortened.

The six selected sources in `NeuralNetworkProofs/` come from [Neural Network Proofs](https://github.com/davorrunje/neural-network-proofs), retrieved on 31 October 2026 from its Lean 4.32.0-rc1 development. Copyright © 2026 Davor Runje. Apache-2.0. They are `ForMathlib/IteratedDerivPolynomial.lean`, `ForMathlib/RidgePowersSpan.lean`, and `UniversalApproximation/Leshno/{ClassM,Family,SmoothEngine,Ridge}.lean`. Only the smooth-activation and ridge-approximation dependency set is included. Module declarations and imports are adapted for Lean 4.35.0; module documentation is shortened. Original copyright and license notices are retained.
