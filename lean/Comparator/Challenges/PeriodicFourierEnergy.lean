module

public import KVApproximation.Analysis.PeriodicSobolev

/-!
# Fourier energy and periodic Korn statements
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: Parseval's identity with
all Euclidean coordinates and the normalized torus measure. -/
theorem hasSum_fourier_energy {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)) :
    HasSum (fun n : Fin d → ℤ => ∑ i,
      ‖∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d‖ ^ 2)
      (‖f‖ ^ 2) := by
  sorry

/-- Section 3.1, periodic Korn argument: the full gradient is controlled
by its ordinary symmetric part, with the exact squared-norm factor two. -/
theorem HasPeriodicWeakGradient.gradient_sq_norm_le_symmetric {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) :
    ‖g‖ ^ 2 ≤ 2 * ‖(symmetrizeL d).compLpL 2 (cellMeasure d) g‖ ^ 2 := by
  sorry

/-- Section 3.1, periodic Korn argument: a zero-mean periodic displacement
is controlled by its gradient. The nonsharp constant one suffices here. -/
theorem HasPeriodicWeakGradient.poincare_sq {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g)
    (hmean : (∫ y, u y ∂cellMeasure d) = 0) :
    ‖u‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  sorry

/-- Section 3.1 (`eq:space_strain_corrector`): the full H¹ norm on
zero-mean periodic displacements admits Korn constant two. -/
theorem periodic_korn_two {d : ℕ} (u : ZeroMeanPeriodicH1 d) :
    ‖u‖ ≤ 2 * ‖correctorGradientL d u‖ := by
  sorry

end KVApproximation.Analysis
