module

public import KVApproximation.OperatorTheory.CoerciveSolverProperties
public import KVApproximation.Dynamics.LinearTimeSobolev
public import KVApproximation.Dynamics.LinearTimeDuhamel

/-!
# Evolution driven by symmetric coercive forms

The viscous solution map turns the tested balance into a bounded linear
evolution equation. Square-integrable dual loads suffice for existence,
uniqueness and the variation-of-constants formula.
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, weak microscopic evolution: bounded symmetric coercive
forms and square-integrable dual forcing give a unique finite-time H¹ solution,
with a common exceptional set before all spatial tests. -/
theorem variational_timeH1_exists_unique (V E : CoerciveForm H)
    {T : ℝ} (hT : 0 < T) (f : ℝ → H →L[ℝ] ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (q₀ : H) :
    ∃! u : TimeH1 H T,
      TimeH1.initial hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : H,
          V.form (TimeH1.velocity u t) v + E.form (TimeH1.value u t) v = f t v := by
  have hiff (u : TimeH1 H T) :
      (TimeH1.initial hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity u t = (-relativeRiesz V E) (TimeH1.value u t) + V.solveL (f t)) ↔
      (TimeH1.initial hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : H,
          V.form (TimeH1.velocity u t) v + E.form (TimeH1.value u t) v = f t v) := by
    apply and_congr_right
    intro _
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun t =>
      (variational_equation_iff V E (TimeH1.velocity u t) (TimeH1.value u t) (f t)).symm
  obtain ⟨u, hu, huniq⟩ := linear_timeH1_exists_unique (-relativeRiesz V E) hT
    (fun t => V.solveL (f t)) (hf.continuousLinearMap_comp V.solveL) q₀
  exact ⟨u, (hiff u).mp hu, fun w hw => huniq w ((hiff w).mpr hw)⟩

/-- Theorem 3.1, Duhamel's formula: the variational evolution is the
homogeneous semigroup plus the time integral of viscously prepared loads. -/
theorem variational_timeH1_duhamel (V E : CoerciveForm H)
    {T : ℝ} (hT : 0 < T) (f : ℝ → H →L[ℝ] ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hu : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : H,
      V.form (TimeH1.velocity u t) v + E.form (TimeH1.value u t) v = f t v)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t =
      (NormedSpace.exp (-(t : ℝ) • relativeRiesz V E)) (TimeH1.initial hT u) +
        ∫ s in (0 : ℝ)..(t : ℝ),
          (NormedSpace.exp (-((t : ℝ) - s) • relativeRiesz V E)) (V.solveL (f s)) := by
  have hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = (-relativeRiesz V E) (TimeH1.value u t) + V.solveL (f t) :=
    hu.mono fun t ht =>
      (variational_equation_iff V E (TimeH1.velocity u t) (TimeH1.value u t) (f t)).mp ht
  simpa only [smul_neg, neg_smul] using linear_timeH1_duhamel (-relativeRiesz V E) hT
    (fun t => V.solveL (f t)) (hf.continuousLinearMap_comp V.solveL) u hode t

end KVApproximation.Dynamics
