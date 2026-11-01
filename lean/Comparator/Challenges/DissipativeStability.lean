module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Stability around a dissipative reference equation
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Dynamics

/-- Proposition B.13, dissipative stability argument: approximation of
a reference field on a closed state tube produces a unique bounded
trajectory with the exact finite-time perturbation bound. -/
theorem dissipative_driven_stability
    {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [FiniteDimensional ℝ Q]
    (e : BoundedTrajectory V) (r : BoundedTrajectory Q)
    (F G : V × Q → Q) (hr : IsKineticSolution e F r)
    {rate δRef margin forcing : ℝ}
    (hRate : 0 < rate) (_hRef : 0 < δRef)
    (hrBound : ∀ t : ℝ, 0 ≤ t → ‖r.value t‖ ≤ δRef)
    (hMargin : 0 < margin) (hforcing : 0 < forcing)
    (hmargin : forcing ≤ rate * margin)
    (hdiss : ∀ (v : V) (q q' : Q),
      ⟪q - q', F (v, q) - F (v, q')⟫_ℝ ≤ -rate * ‖q - q'‖ ^ 2)
    (hG : LocallyLipschitz G)
    (happrox : ∀ (v : V) (q : Q), ‖v‖ ≤ e.velocityBound →
      ‖q‖ ≤ δRef + margin → ‖G (v, q) - F (v, q)‖ ≤ forcing) :
    ∃ q : BoundedTrajectory Q, IsKineticSolution e G q ∧
      (∀ q' : BoundedTrajectory Q, IsKineticSolution e G q' → q.Agree q') ∧
      (∀ t : ℝ, 0 ≤ t → ‖q.value t - r.value t‖ ≤
        forcing / rate * (1 - Real.exp (-rate * t))) := by
  sorry

end KVApproximation.Dynamics
