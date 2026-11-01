module

public import KVApproximation.Homogenization.HomogenizedMemory
public import KVApproximation.Homogenization.ConstantSpatialCoercivity
public import KVApproximation.Analysis.TimeSobolevMemoryUniqueness

/-!
# Uniqueness of the homogenized weak solution

Elastic coercivity identifies the prepared initial state. Viscous coercivity
then supplies the norm bound for finite-time Sobolev memory uniqueness.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, uniqueness: an L² load is integrable on the finite horizon. -/
private theorem intervalIntegrable_of_memLp_two {G : Type*}
    [NormedAddCommGroup G] {T : ℝ} (hT : 0 ≤ T) {g : ℝ → G}
    (hg : MemLp g 2 (volume.restrict (Set.Ioo 0 T))) :
    IntervalIntegrable g volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).2
    (hg.integrable (by norm_num))

/-- Theorem 3.1, uniqueness: elastic injectivity identifies the initial
trace before the viscous bound is applied to the memory equation. -/
private theorem memory_unique_of_prepared {H F G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℝ} (hT : 0 < T) (u v : TimeH1 H T)
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (g : ℝ → G)
    (hg : IntervalIntegrable g volume 0 T)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ x : H, ‖x‖ ≤ C * ‖V x‖)
    (hE : ∃ C : ℝ, 0 < C ∧ ∀ x : H, ‖x‖ ≤ C * ‖E x‖)
    (hinit : E (TimeH1.initial hT u) = E (TimeH1.initial hT v))
    (hu : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = g t)
    (hv : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity v t) + E (TimeH1.value v t) +
        posConvolution K (TimeH1.velocity v) L volume t = g t) : u = v := by
  obtain ⟨CE, _, hEbound⟩ := hE
  have hinit' : TimeH1.initial hT u = TimeH1.initial hT v := by
    apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp
    have h := hEbound (TimeH1.initial hT u - TimeH1.initial hT v)
    rw [map_sub, hinit, sub_self, norm_zero, mul_zero] at h
    exact h
  obtain ⟨CV, hCV, hVbound⟩ := hV
  exact TimeH1.eq_of_memory_equation hT u v V E L K hK g hg
    CV hCV.le hVbound hinit' hu hv

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedUniqueness.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedUniqueness.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedUniqueness.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedUniqueness.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), uniqueness: the
actual homogenized weak equation and prepared initial condition have at most
one finite-horizon Sobolev solution. -/
theorem homogenized_solution_unique
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (Vhom Ehom : Elasticity d)
    (hV : PositiveDefinite Vhom) (hE : PositiveDefinite Ehom)
    (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ : SpatialL2 Ω) (f : Forcing Ω T) (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K g₀ f u)
    (hv : IsHomogenizedSolution hT Vhom Ehom K g₀ f v) : u = v := by
  have hu' := (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK g₀ f u).mp hu
  have hv' := (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK g₀ f v).mp hv
  have hgf : MemLp (fun t => spatialLoadOperator (Ω := Ω) (f t)) 2
      (volume.restrict (Set.Ioo 0 T)) :=
    (Lp.memLp f).continuousLinearMap_comp (spatialLoadOperator (Ω := Ω))
  have hg : IntervalIntegrable (fun t => spatialLoadOperator (Ω := Ω) (f t)) volume 0 T :=
    intervalIntegrable_of_memLp_two hT.le hgf
  exact memory_unique_of_prepared hT u v
    (constantSpatialFormL (Ω := Ω) Vhom) (constantSpatialFormL (Ω := Ω) Ehom)
    (constantSpatialFormL (Ω := Ω)) K hK
    (fun t => spatialLoadOperator (Ω := Ω) (f t)) hg
    (exists_constantSpatialFormL_norm_bound Vhom hV hΩ)
    (exists_constantSpatialFormL_norm_bound Ehom hE hΩ)
    (hu'.1.trans hv'.1.symm) hu'.2 hv'.2

end KVApproximation.Homogenization
