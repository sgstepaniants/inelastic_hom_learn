module

public import KVApproximation.Analysis.VectorSobolev
public import KVApproximation.Analysis.LpFiniteCoordinates
public import KVApproximation.Analysis.LpCoordinates
public import KVApproximation.Tensor.Symmetrization

/-!
# Displacement and gradient fields on an open domain
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 2.1, spatial derivative convention: gradient rows and
physical-index matrices have the same Frobenius norm. -/
def gradientRowCoordinates (d : ℕ) :
    PiLp 2 (fun _ : Fin d => PhysicalSpace d) ≃ₗᵢ[ℝ] SecondOrder d :=
  (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ _ : Fin d) => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd (Fin d) (Fin d)))

/-- Theorem 3.1, spatial Sobolev foundations: the full weak gradient,
with displacement component first and derivative direction second. -/
def VectorH1.gradient {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (u : VectorH1 Ω) (x : PhysicalSpace d) : SecondOrder d :=
  WithLp.toLp 2 (fun ij => VectorH1.gradientEntry u x ij.1 ij.2)

/-- Theorem 3.1, spatial Sobolev foundations: the strain representative
for an arbitrary H¹ displacement. -/
def VectorH1.symmetricGradient {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (u : VectorH1 Ω) (x : PhysicalSpace d) : Symmetric d :=
  symmetrize (VectorH1.gradient u x)

/-- Theorem 3.1, spatial Sobolev foundations: displacement as a bounded
linear map into the actual vector-valued L² space. -/
def VectorH1.valueL {d : ℕ} (Ω : Opens (PhysicalSpace d)) :
    VectorH1 Ω →L[ℝ] Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  let U := (lp_finite_coordinates (E := fun _ : Fin d => ℝ) (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
  let C := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d))))).symm.toContinuousLinearMap
  U.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (C.comp (ContinuousLinearMap.pi fun i =>
      TauCeti.W1p.valueL.comp (PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Fin d => TauCeti.W1p volume Ω 2) i)))

/-- Theorem 3.1, spatial Sobolev foundations: full gradient as a bounded
linear map into Frobenius-valued L². -/
def VectorH1.gradientL {d : ℕ} (Ω : Opens (PhysicalSpace d)) :
    VectorH1 Ω →L[ℝ] Lp (SecondOrder d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  let U := (lp_finite_coordinates (E := fun _ : Fin d => PhysicalSpace d)
    (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
  let V := (lp_coordinates (volume.restrict (Ω : Set (PhysicalSpace d))) 2 (gradientRowCoordinates d)).choose
  let C := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))).symm.toContinuousLinearMap
  V.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (C.comp (ContinuousLinearMap.pi fun i =>
        TauCeti.W1p.gradientL.comp (PiLp.proj (𝕜 := ℝ) 2
          (fun _ : Fin d => TauCeti.W1p volume Ω 2) i))))

/-- Theorem 3.1, spatial Sobolev foundations: strain as a bounded linear
map with the physical-index Frobenius norm. -/
def VectorH1.symmetricGradientL {d : ℕ} (Ω : Opens (PhysicalSpace d)) :
    VectorH1 Ω →L[ℝ] Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  ((symmetrizeL d).compLpL 2 (volume.restrict (Ω : Set (PhysicalSpace d)))).comp (VectorH1.gradientL Ω)

end KVApproximation.Analysis
