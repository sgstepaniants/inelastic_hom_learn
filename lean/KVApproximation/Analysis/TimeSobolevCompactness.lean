module

public import KVApproximation.Analysis.TimeSobolevNorms
public import KVApproximation.Analysis.HilbertWeakCompactness
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak compactness of finite-time H¹ trajectories
-/

public section

noncomputable section

open Filter
open scoped Topology InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, time-space compactness: two Hilbert coordinates induce
an inner product whenever their squared norms sum to the existing squared norm. -/
@[expose, instance_reducible] def TimeSobolevCompactness.innerProductSpaceOfCoordinates
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : E →L[ℝ] F) (g : E →L[ℝ] G)
    (h : ∀ u, ‖u‖ ^ 2 = ‖f u‖ ^ 2 + ‖g u‖ ^ 2) : InnerProductSpace ℝ E where
  toNormedSpace := inferInstance
  inner u v := ⟪f u, f v⟫_ℝ + ⟪g u, g v⟫_ℝ
  norm_sq_eq_re_inner u := by
    simpa only [RCLike.re_to_real, real_inner_self_eq_norm_sq] using h u
  conj_inner_symm u v := by
    change ⟪f v, f u⟫_ℝ + ⟪g v, g u⟫_ℝ = ⟪f u, f v⟫_ℝ + ⟪g u, g v⟫_ℝ
    exact congrArg₂ (· + ·) (real_inner_comm _ _) (real_inner_comm _ _)
  add_left u v w := by
    simp only [map_add, inner_add_left]
    ring
  smul_left u v r := by
    simp only [map_smul, real_inner_smul_left, conj_trivial, mul_add]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, time-space compactness: the value and velocity inner products
induce the existing H¹ graph norm and preserve its normed-space structure. -/
@[expose, instance_reducible] def TimeSobolevCompactness.instInnerProductSpace {T : ℝ} :
    InnerProductSpace ℝ (TimeH1 H T) :=
  TimeSobolevCompactness.innerProductSpaceOfCoordinates TimeH1.valueL2 TimeH1.velocityL2
    TimeH1.norm_sq_eq_value_velocity

attribute [local instance] TimeSobolevCompactness.instInnerProductSpace

/-- Theorem 3.1, time-space compactness: a bounded sequence in the actual
finite-time H¹ space has a weakly convergent subsequence with the same norm bound. -/
theorem TimeH1.exists_weakly_convergent_subsequence {T : ℝ}
    (u : ℕ → TimeH1 H T) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : TimeH1 H T, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  exact KVApproximation.Analysis.exists_weakly_convergent_subsequence u hu

/-- Theorem 3.1, compatibility of time-space limits: weak H¹ convergence
gives weak convergence of the continuous trace at every time, including both endpoints. -/
theorem TimeH1.weak_trace_tendsto {I : Type*} {l : Filter I} {T : ℝ}
    (hT : 0 < T) (u : I → TimeH1 H T) (uLim : TimeH1 H T)
    (hu : ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (u i)) l (𝓝 (ℓ uLim)))
    (t : Set.Icc (0 : ℝ) T) (ℓ : H →L[ℝ] ℝ) :
    Tendsto (fun i => ℓ (TimeH1.trace hT (u i) t)) l
      (𝓝 (ℓ (TimeH1.trace hT uLim t))) := by
  exact hu (ℓ.comp ((ContinuousMap.evalCLM ℝ t).comp
    (TauCeti.EvolutionSpace.toContinuousMap (ι := ContinuousLinearMap.id ℝ H) hT)))

end KVApproximation.Analysis
