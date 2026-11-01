module

public import KVApproximation.OperatorTheory.CoerciveSolvers
public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Analysis.SpecialFunctions.Exponential

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
  sorry

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
  sorry

end KVApproximation.Dynamics
