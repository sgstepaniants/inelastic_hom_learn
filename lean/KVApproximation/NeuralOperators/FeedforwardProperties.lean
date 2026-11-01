module

public import KVApproximation.NeuralOperators.Feedforward
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Regularity of finite feedforward networks
-/

public section

namespace KVApproximation.NeuralOperators

/-- Remarks 4.2–4.3: scalar Lipschitz bounds pass to Euclidean coordinate activation. -/
private theorem lipschitz_activation {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) (n : ℕ) :
    LipschitzWith K (fun x : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (fun i => σ (x i))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).mp
  rw [PiLp.dist_sq_eq_of_L2, mul_pow, PiLp.dist_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change dist (σ (x i)) (σ (y i)) ^ 2 ≤ (K : ℝ) ^ 2 * dist (x i) (y i) ^ 2
  simpa only [mul_pow] using
    pow_le_pow_left₀ dist_nonneg (hσ.dist_le_mul (x i) (y i)) 2

/-- Remarks 4.2–4.3: a compact scalar interval supplies a common local
Lipschitz bound for all coordinates near a given finite vector. -/
private theorem locallyLipschitz_activation {σ : ℝ → ℝ}
    (hσ : LocallyLipschitz σ) (n : ℕ) :
    LocallyLipschitz (fun x : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (fun i => σ (x i))) := by
  intro x
  let R : ℝ := ‖x‖ + 1
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := Set.Icc (-R) R) isCompact_Icc hσ.locallyLipschitzOn
  obtain ⟨g, hg, hsame⟩ := hK.extend_real
  have heq (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball x 1) :
      WithLp.toLp 2 (fun i => σ (z i)) = WithLp.toLp 2 (fun i => g (z i)) := by
    apply congrArg (WithLp.toLp 2)
    funext i
    apply hsame
    have hzR : ‖z‖ ≤ R := norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hz).le
    have hcoord : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    have hi : |z i| ≤ R := hcoord.trans hzR
    exact abs_le.mp hi
  refine ⟨K, Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  intro z hz w hw
  dsimp only
  rw [heq z hz, heq w hw]
  exact lipschitz_activation hg n z w

/-- Remarks 4.2–4.3: finite-dimensional affine maps are globally Lipschitz. -/
private theorem lipschitz_affine {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (A : E →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) :
    LipschitzWith ‖A.toContinuousLinearMap‖₊ (fun x => A x + b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_right, LinearMap.coe_toContinuousLinearMap'] using
    A.toContinuousLinearMap.lipschitzWith.dist_le_mul x y

/-- Example 2.1 and Remarks 4.2–4.3: globally Lipschitz activations give a
globally Lipschitz finite feedforward network on its full input space. -/
theorem Feedforward.lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {output : ℕ} (P : Feedforward E output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) : ∃ L : NNReal, LipschitzWith L (P.eval σ) := by
  induction P with
  | affine A b => exact ⟨_, lipschitz_affine A b⟩
  | layer previous A b ih =>
      obtain ⟨L, hL⟩ := ih
      exact ⟨_, (lipschitz_affine A b).comp ((lipschitz_activation hσ _).comp hL)⟩

/-- Remarks 4.2–4.3: locally Lipschitz activations suffice for the
finite-dimensional feedforward output map to be locally Lipschitz. -/
theorem Feedforward.locallyLipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {output : ℕ} (P : Feedforward E output) {σ : ℝ → ℝ}
    (hσ : LocallyLipschitz σ) : LocallyLipschitz (P.eval σ) := by
  induction P with
  | affine A b => exact (lipschitz_affine A b).locallyLipschitz
  | layer previous A b ih =>
      exact (lipschitz_affine A b).locallyLipschitz.comp
        ((locallyLipschitz_activation hσ _).comp ih)

end KVApproximation.NeuralOperators
