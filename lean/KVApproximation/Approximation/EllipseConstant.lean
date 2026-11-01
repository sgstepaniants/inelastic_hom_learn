import KVApproximation.Approximation.Constants
import LeanCert.Tactic.IntervalAuto.PointIneq

/-!
# The fixed Bernstein-ellipse constant
-/

set_option leancert.trust "kernel"

namespace KVApproximation.Approximation

/-- Lemma B.9, supporting numerical certificate: positivity of the cosine
in the exact ellipse constant. This is not a separate numbered paper result. -/
theorem cos_three_quarters_lower :
    (7 : ℝ) / 10 < Real.cos (3 / 4 : ℝ) := by
  interval_decide 3

/-- Lemma B.9, proof: the ellipse parameter two has imaginary semiaxis 3/4. -/
theorem bernsteinImaginarySemiaxis_two :
    bernsteinImaginarySemiaxis 2 = (3 : ℝ) / 4 := by
  norm_num [bernsteinImaginarySemiaxis]

end KVApproximation.Approximation
