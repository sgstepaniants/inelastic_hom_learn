module

public import KVApproximation.Analysis.VectorSobolevFields
public import KVApproximation.Tensor.SymmetrizationProperties

/-!
# Spatial Sobolev fields and the full H¹ norm
-/

public section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

private theorem valueL_coordinates (u : VectorH1 Ω) :
    VectorH1.valueL Ω u = (lp_finite_coordinates (E := fun _ : Fin d => ℝ)
      (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
        (WithLp.toLp 2 (fun i => TauCeti.W1p.value (u i))) := by
  change (lp_finite_coordinates (E := fun _ : Fin d => ℝ)
    (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
      (WithLp.toLp 2 (fun i => TauCeti.W1p.valueL (u i))) = _
  simp only [TauCeti.W1p.valueL_apply]

private theorem gradientL_coordinates (u : VectorH1 Ω) :
    VectorH1.gradientL Ω u = (lp_coordinates (volume.restrict (Ω : Set (PhysicalSpace d))) 2
      (gradientRowCoordinates d)).choose
        ((lp_finite_coordinates (E := fun _ : Fin d => PhysicalSpace d)
          (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
            (WithLp.toLp 2 (fun i => TauCeti.W1p.gradient (u i)))) := by
  change (lp_coordinates (volume.restrict (Ω : Set (PhysicalSpace d))) 2
    (gradientRowCoordinates d)).choose
      ((lp_finite_coordinates (E := fun _ : Fin d => PhysicalSpace d)
        (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
          (WithLp.toLp 2 (fun i => TauCeti.W1p.gradientL (u i)))) = _
  simp only [TauCeti.W1p.gradientL_apply]

/-- Theorem 3.1, spatial Sobolev foundations: the L² value map represents
the displacement defined componentwise in Section 2.1. -/
theorem VectorH1.valueL_apply_ae (u : VectorH1 Ω) :
    ∀ᵐ x ∂volume.restrict Ω, VectorH1.valueL Ω u x = VectorH1.value u x := by
  rw [valueL_coordinates]
  exact (lp_finite_coordinates (E := fun _ : Fin d => ℝ)
    (volume.restrict (Ω : Set (PhysicalSpace d)))).choose_spec
      (WithLp.toLp 2 (fun i => TauCeti.W1p.value (u i)))

/-- Theorem 3.1, spatial Sobolev foundations: the L² gradient map
represents the actual full weak derivative. -/
theorem VectorH1.gradientL_apply_ae (u : VectorH1 Ω) :
    ∀ᵐ x ∂volume.restrict Ω, VectorH1.gradientL Ω u x = VectorH1.gradient u x := by
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let f : PiLp 2 (fun _ : Fin d => Lp (PhysicalSpace d) 2 μ) :=
    WithLp.toLp 2 (fun i => TauCeti.W1p.gradient (u i))
  let U := (lp_finite_coordinates (E := fun _ : Fin d => PhysicalSpace d) μ).choose
  let V := (lp_coordinates μ 2 (gradientRowCoordinates d)).choose
  have hU := (lp_finite_coordinates (E := fun _ : Fin d => PhysicalSpace d) μ).choose_spec f
  have hV := (lp_coordinates μ 2 (gradientRowCoordinates d)).choose_spec (U f)
  rw [gradientL_coordinates]
  filter_upwards [hU, hV] with x hx hy
  change V (U f) x = VectorH1.gradient u x
  rw [hy, hx]
  rfl

/-- Theorem 3.1, spatial Sobolev foundations: the L² strain map
represents the symmetric weak derivative. -/
theorem VectorH1.symmetricGradientL_apply_ae (u : VectorH1 Ω) :
    ∀ᵐ x ∂volume.restrict Ω,
      VectorH1.symmetricGradientL Ω u x = VectorH1.symmetricGradient u x := by
  have h := (Tensor.symmetrizeL d).coeFn_compLp (VectorH1.gradientL Ω u)
  filter_upwards [h, VectorH1.gradientL_apply_ae u] with x hx hg
  change (Tensor.symmetrizeL d).compLp (VectorH1.gradientL Ω u) x = _
  rw [hx, hg]
  rfl

/-- Theorem 3.1, spatial Sobolev foundations: the squared displacement
norm is the sum of the squared scalar component norms. -/
theorem VectorH1.norm_valueL_sq (u : VectorH1 Ω) :
    ‖VectorH1.valueL Ω u‖ ^ 2 = ∑ i, ‖TauCeti.W1p.value (u i)‖ ^ 2 := by
  rw [valueL_coordinates, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]

/-- Theorem 3.1, spatial Sobolev foundations: the squared Frobenius
gradient norm is the sum of the squared gradient-row norms. -/
theorem VectorH1.norm_gradientL_sq (u : VectorH1 Ω) :
    ‖VectorH1.gradientL Ω u‖ ^ 2 = ∑ i, ‖TauCeti.W1p.gradient (u i)‖ ^ 2 := by
  rw [gradientL_coordinates, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    PiLp.norm_sq_eq_of_L2]

/-- Theorem 3.1, spatial Sobolev foundations: the full H¹ norm is exactly
the Euclidean combination of displacement and Frobenius gradient norms. -/
theorem VectorH1.norm_sq_eq (u : VectorH1 Ω) :
    ‖u‖ ^ 2 = ‖VectorH1.valueL Ω u‖ ^ 2 + ‖VectorH1.gradientL Ω u‖ ^ 2 := by
  rw [VectorH1.norm_valueL_sq, VectorH1.norm_gradientL_sq,
    PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (u i)

/-- Theorem 3.1, spatial Sobolev foundations: the value map has norm at
most one, independently of the domain and physical dimension. -/
theorem VectorH1.norm_valueL_le (u : VectorH1 Ω) :
    ‖VectorH1.valueL Ω u‖ ≤ ‖u‖ := by
  have h := VectorH1.norm_sq_eq u
  nlinarith [sq_nonneg ‖VectorH1.gradientL Ω u‖, norm_nonneg u,
    norm_nonneg (VectorH1.valueL Ω u)]

/-- Theorem 3.1, spatial Sobolev foundations: the full gradient map has
norm at most one for the full H¹ norm. -/
theorem VectorH1.norm_gradientL_le (u : VectorH1 Ω) :
    ‖VectorH1.gradientL Ω u‖ ≤ ‖u‖ := by
  have h := VectorH1.norm_sq_eq u
  nlinarith [sq_nonneg ‖VectorH1.valueL Ω u‖, norm_nonneg u,
    norm_nonneg (VectorH1.gradientL Ω u)]

/-- Theorem 3.1, spatial Sobolev foundations: symmetrization contracts
the Frobenius L² gradient norm without a dimension factor. -/
theorem VectorH1.norm_symmetricGradientL_le (u : VectorH1 Ω) :
    ‖VectorH1.symmetricGradientL Ω u‖ ≤ ‖VectorH1.gradientL Ω u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have h := (Tensor.symmetrizeL d).coeFn_compLp (VectorH1.gradientL Ω u)
  filter_upwards [h] with x hx
  change ‖(Tensor.symmetrizeL d).compLp (VectorH1.gradientL Ω u) x‖ ≤ _
  rw [hx]
  exact Tensor.norm_symmetrize_le (VectorH1.gradientL Ω u x)

/-- Theorem 3.1, spatial Sobolev foundations: a displacement determines
its weak derivatives, so equality of L² values determines the H¹ jet. -/
theorem VectorH1.valueL_injective : Function.Injective (VectorH1.valueL Ω) := by
  intro u v h
  rw [valueL_coordinates, valueL_coordinates] at h
  have hc := (lp_finite_coordinates (E := fun _ : Fin d => ℝ)
    (volume.restrict (Ω : Set (PhysicalSpace d)))).choose.injective h
  apply PiLp.ext
  intro i
  have hi := congrFun (congrArg WithLp.ofLp hc) i
  exact TauCeti.W1p.ext_value (u := u i) (v := v i) hi

end KVApproximation.Analysis
