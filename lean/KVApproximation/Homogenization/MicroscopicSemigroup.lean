module

public import KVApproximation.Homogenization.SpatialEvolutionProperties
public import KVApproximation.OperatorTheory.VariationalSemigroup

/-!
# Uniform microscopic homogeneous evolution

The spatial viscous energy controls displacement and velocity on the
whole nonnegative time axis, uniformly in the periodic scale.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicSemigroup.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicSemigroup.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicSemigroup.instTopologicalRing : IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ) (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, homogeneous microscopic evolution: the actual spatial
semigroup has its prescribed Hilbert-valued derivative. -/
theorem microscopic_homogeneous_hasDerivAt (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (NormedSpace.exp (-s • microscopicRelaxation V E hΩ ε hε)) q)
      (-microscopicRelaxation V E hΩ ε hε
        ((NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q)) t := by
  exact relativeSemigroup_hasDerivAt (H := ZeroBoundaryH1 Ω) (periodicSpatialForm V hΩ ε hε)
    (periodicSpatialForm E hΩ ε hε) q t

/-- Theorem 3.1, uniform half-line estimate: one constant bounds the
actual homogeneous spatial trajectory and its velocity at every nonnegative
time, before choosing the microscopic scale or initial displacement. -/
theorem exists_uniform_microscopic_semigroup_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω)
      (t : ℝ), 0 ≤ t →
      ‖(NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q‖ ≤ C * ‖q‖ ∧
      ‖-microscopicRelaxation V E hΩ ε hε
        ((NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q)‖ ≤ C * ‖q‖ := by
  have hbounds := exists_uniform_periodicSpatialForm_bounds (Ω := Ω) V hΩ
  let α := hbounds.choose
  let β := hbounds.choose_spec.choose
  have hα : 0 < α := hbounds.choose_spec.choose_spec.1
  have hβ : 0 < β := hbounds.choose_spec.choose_spec.2.1
  have hV := hbounds.choose_spec.choose_spec.2.2
  have hopbounds := exists_uniform_microscopic_operator_bounds (Ω := Ω) V E hΩ
  let B := hopbounds.choose
  have hB : 0 < B := hopbounds.choose_spec.1
  have hoperators := hopbounds.choose_spec.2
  let S : ℝ := Real.sqrt (β / α)
  have hS : 0 < S := Real.sqrt_pos.2 (div_pos hβ hα)
  refine ⟨S * (B + 1), mul_pos hS (by linarith), ?_⟩
  intro ε hε q t ht
  have hvalue : ‖(NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q‖ ≤
      S * ‖q‖ :=
    relativeSemigroup_norm_le (H := ZeroBoundaryH1 Ω) (periodicSpatialForm V hΩ ε hε)
      (periodicSpatialForm E hΩ ε hε) hα hβ.le (hV ε hε) q t ht
  have hSle : S ≤ S * (B + 1) := by nlinarith [mul_nonneg hS.le hB.le]
  have hBSle : B * S ≤ S * (B + 1) := by nlinarith [hS.le]
  constructor
  · exact hvalue.trans (mul_le_mul_of_nonneg_right hSle (norm_nonneg q))
  · rw [norm_neg]
    calc
      _ ≤ B * ‖(NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q‖ :=
        (hoperators ε hε).1 _
      _ ≤ B * (S * ‖q‖) := mul_le_mul_of_nonneg_left hvalue hB.le
      _ = (B * S) * ‖q‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBSle (norm_nonneg q)

end KVApproximation.Homogenization
