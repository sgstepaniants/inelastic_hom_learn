module

public import KVApproximation.KelvinVoigt.StripFields
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Convergence of the thin-strip coefficients
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient convergence:
the exact finite-exponent seminorm of the strip perturbation uses its width
and the Frobenius norm of the identity tensor. -/
theorem eLpNorm_stripElasticity_sub_identity {d : ℕ} (i : Fin d) (m : ℕ)
    {p : ENNReal} (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (fun y => stripElasticity i m y - identityElasticity d) p (cellMeasure d) =
      ENNReal.ofReal ‖identityElasticity d‖ *
        (ENNReal.ofReal (1 / ((m : ℝ) + 1))) ^ (1 / p.toReal) := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient convergence:
the strip elasticities converge to the identity in every finite positive
Lp seminorm, in particular the paper's L¹ and L² topologies. -/
theorem tendsto_eLpNorm_stripElasticity_sub_identity {d : ℕ} (i : Fin d)
    {p : ENNReal} (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    Tendsto (fun m =>
      eLpNorm (fun y => stripElasticity i m y - identityElasticity d) p (cellMeasure d))
      atTop (𝓝 0) := by
  sorry

end KVApproximation.KelvinVoigt
