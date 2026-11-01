module

public import KVApproximation.KelvinVoigt.StripFields
public import KVApproximation.Analysis.PeriodicVariation

/-!
# Uniform bounds for the thin-strip coefficients
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient bounds:
the normalized-cell Lp seminorm of the strip elasticity is at most twice
the Frobenius norm of the identity, for every exponent. -/
theorem eLpNorm_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) (p : ENNReal) :
    eLpNorm (stripElasticity i m) p (cellMeasure d) ≤
      ENNReal.ofReal (2 * ‖identityElasticity d‖) := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
the two periodic faces give a uniform bound independent of the width. -/
theorem periodicVariation_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) :
    periodicVariation (stripElasticity i m) ≤ ENNReal.ofReal (2 * ‖identityElasticity d‖) := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), limiting material:
the full BV norm of the constant identity field equals its Frobenius norm. -/
theorem periodicBVNorm_identityElasticity (d : ℕ) :
    periodicBVNorm (fun _ : PeriodicCell d => identityElasticity d) =
      ENNReal.ofReal ‖identityElasticity d‖ := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), common admissible class:
the L¹ and variation terms give one uniform full BV bound. -/
theorem periodicBVNorm_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) :
    periodicBVNorm (stripElasticity i m) ≤ ENNReal.ofReal (4 * ‖identityElasticity d‖) := by
  sorry

end KVApproximation.KelvinVoigt
