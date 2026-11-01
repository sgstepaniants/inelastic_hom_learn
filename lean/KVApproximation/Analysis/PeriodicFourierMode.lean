module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Real Fourier modes with Euclidean amplitudes
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

/-- Section 3.1, smooth density argument: the real part of a complex
Fourier mode, with a separate amplitude in every Euclidean coordinate. -/
def realFourierMode {d : ℕ} {ι : Type*} [Fintype ι]
    (n : Fin d → ℤ) (a : ι → ℂ) : C(PeriodicCell d, EuclideanSpace ℝ ι) where
  toFun y := WithLp.toLp 2 (fun i => (a i * UnitAddTorus.mFourier n y).re)
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
    (continuous_pi fun i => Complex.continuous_re.comp
      ((continuous_const (y := a i)).mul (UnitAddTorus.mFourier n).continuous))

end KVApproximation.Analysis
