module

public import KVApproximation.Analysis.DirichletPoincare
public import KVApproximation.Analysis.DirichletMixedDerivatives

/-!
# Korn estimates for zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Tensor

namespace KVApproximation.Analysis

private theorem norm_sq_of_ae_coordinates {X ι F : Type*}
    [MeasurableSpace X] [Fintype ι] [NormedAddCommGroup F]
    {μ : Measure X} (f : Lp F 2 μ) (c : ι → Lp ℝ 2 μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 = ∑ i, ‖c i x‖ ^ 2) :
    ‖f‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ x, ∑ i, ‖c i x‖ ^ 2 ∂μ := integral_congr_ae h
    _ = ∑ i, ∫ x, ‖c i x‖ ^ 2 ∂μ :=
      integral_finsetSum Finset.univ fun i _ => (Lp.memLp (c i)).norm.integrable_sq
    _ = _ := Finset.sum_congr rfl fun i _ => Lp.integral_norm_sq_eq_norm_sq (c i)

private theorem symmetric_array_energy {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a : ι × ι → H) :
    2 * (∑ ij, ‖(1 / 2 : ℝ) • (a ij + a (ij.2, ij.1))‖ ^ 2) =
      (∑ ij, ‖a ij‖ ^ 2) + ∑ ij, ⟪a ij, a (ij.2, ij.1)⟫_ℝ := by
  have hs (ij : ι × ι) :
      2 * ‖(1 / 2 : ℝ) • (a ij + a (ij.2, ij.1))‖ ^ 2 =
        (‖a ij‖ ^ 2 + ‖a (ij.2, ij.1)‖ ^ 2) / 2 +
          ⟪a ij, a (ij.2, ij.1)⟫_ℝ := by
    rw [norm_smul, mul_pow, norm_add_sq_real]
    norm_num
    ring
  have ht : (∑ ij : ι × ι, ‖a (ij.2, ij.1)‖ ^ 2) = ∑ ij, ‖a ij‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [Finset.mul_sum]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ht]
  ring

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

private theorem directional_coordinates (u : VectorH1 Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)), ∀ ij : Fin d × Fin d,
      directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ ij.2)
        (u ij.1) x = VectorH1.gradientEntry u x ij.1 ij.2 := by
  apply ae_all_iff.mpr
  intro ij
  filter_upwards [directionalDerivativeL_apply_ae
    (EuclideanSpace.basisFun (Fin d) ℝ ij.2) (u ij.1)] with x hx
  rw [hx, EuclideanSpace.basisFun_inner]
  rfl

private theorem gradient_energy_coordinates (u : VectorH1 Ω) :
    ‖VectorH1.gradientL Ω u‖ ^ 2 = ∑ ij : Fin d × Fin d,
      ‖directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ ij.2)
        (u ij.1)‖ ^ 2 := by
  apply norm_sq_of_ae_coordinates
  filter_upwards [VectorH1.gradientL_apply_ae u, directional_coordinates u] with x hx hc
  rw [hx, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hc ij]
  rfl

private theorem strain_energy_coordinates (u : VectorH1 Ω) :
    ‖VectorH1.symmetricGradientL Ω u‖ ^ 2 = ∑ ij : Fin d × Fin d,
      ‖(1 / 2 : ℝ) •
        (directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ ij.2) (u ij.1) +
          directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ ij.1) (u ij.2))‖ ^ 2 := by
  let a (ij : Fin d × Fin d) :=
    directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ ij.2) (u ij.1)
  have hs (ij : Fin d × Fin d) :
      ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
        ((1 / 2 : ℝ) • (a ij + a (ij.2, ij.1))) x =
          (a ij x + a (ij.2, ij.1) x) / 2 := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (a ij + a (ij.2, ij.1)),
      Lp.coeFn_add (a ij) (a (ij.2, ij.1))] with x hsm ha
    rw [hsm]
    change (1 / 2 : ℝ) * (a ij + a (ij.2, ij.1)) x = _
    rw [ha]
    change (1 / 2 : ℝ) * (a ij x + a (ij.2, ij.1) x) = _
    ring
  apply norm_sq_of_ae_coordinates
  filter_upwards [VectorH1.symmetricGradientL_apply_ae u, directional_coordinates u,
    ae_all_iff.mpr hs] with x hx hc hh
  rw [hx]
  change ‖(symmetrize (VectorH1.gradient u x)).val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hh ij]
  change ‖(VectorH1.gradientEntry u x ij.1 ij.2 +
    VectorH1.gradientEntry u x ij.2 ij.1) / 2‖ ^ 2 =
      ‖(a ij x + a (ij.2, ij.1) x) / 2‖ ^ 2
  rw [hc ij, hc (ij.2, ij.1)]

/-- Theorem 3.1, spatial coercivity: the exact strain-energy identity
on H¹₀, with the divergence formed in scalar L². -/
theorem ZeroBoundaryH1.korn_identity (u : ZeroBoundaryH1 Ω) :
    2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 =
      ‖VectorH1.gradientL Ω u.val‖ ^ 2 +
        ‖∑ i : Fin d, directionalDerivativeL volume Ω
          (EuclideanSpace.basisFun (Fin d) ℝ i) (u.val i)‖ ^ 2 := by
  rw [strain_energy_coordinates, gradient_energy_coordinates, symmetric_array_energy]
  congr 1
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j,
        ⟪directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ i) (u.val i),
          directionalDerivativeL volume Ω (EuclideanSpace.basisFun (Fin d) ℝ j) (u.val j)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact inner_directionalDerivative_swap (u.val i) (u.val j)
        ((mem_zeroBoundary_iff u.val).mp u.property i) _ _
    _ = _ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [sum_inner, inner_sum]
      exact Finset.sum_comm

/-- Theorem 3.1, spatial coercivity: the Dirichlet Korn inequality
has squared constant two, independently of domain and dimension. -/
theorem ZeroBoundaryH1.norm_gradientL_sq_le (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.gradientL Ω u.val‖ ^ 2 ≤
      2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 := by
  rw [ZeroBoundaryH1.korn_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Theorem 3.1, spatial coercivity: the full weak gradient is
bounded by √2 times the symmetric gradient. -/
theorem ZeroBoundaryH1.norm_gradientL_le (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.gradientL Ω u.val‖ ≤
      Real.sqrt 2 * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
  apply (sq_le_sq₀ (norm_nonneg (VectorH1.gradientL Ω u.val))
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (VectorH1.symmetricGradientL Ω u.val)))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact ZeroBoundaryH1.norm_gradientL_sq_le u

/-- Theorem 3.1, spatial coercivity: on a bounded domain, the strain
controls the full H¹ norm with a positive constant independent of
the microscopic coefficients and their scale. -/
theorem ZeroBoundaryH1.exists_korn_constant
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖u‖ ≤ C * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
  obtain ⟨C, hC, hp⟩ := ZeroBoundaryH1.exists_poincare_constant hΩ
  refine ⟨(C + 1) * Real.sqrt 2, mul_pos (by linarith) (Real.sqrt_pos.mpr (by norm_num)), ?_⟩
  intro u
  have hn : ‖u‖ ≤ ‖VectorH1.valueL Ω u.val‖ + ‖VectorH1.gradientL Ω u.val‖ := by
    have he := VectorH1.norm_sq_eq u.val
    have hprod := mul_nonneg (norm_nonneg (VectorH1.valueL Ω u.val))
      (norm_nonneg (VectorH1.gradientL Ω u.val))
    change ‖u.val‖ ≤ _
    nlinarith [norm_nonneg u.val, norm_nonneg (VectorH1.valueL Ω u.val),
      norm_nonneg (VectorH1.gradientL Ω u.val)]
  calc
    ‖u‖ ≤ ‖VectorH1.valueL Ω u.val‖ + ‖VectorH1.gradientL Ω u.val‖ := hn
    _ ≤ (C + 1) * ‖VectorH1.gradientL Ω u.val‖ := by nlinarith [hp u]
    _ ≤ (C + 1) * (Real.sqrt 2 * ‖VectorH1.symmetricGradientL Ω u.val‖) :=
      mul_le_mul_of_nonneg_left (ZeroBoundaryH1.norm_gradientL_le u) (by linarith)
    _ = _ := by ring

end KVApproximation.Analysis
