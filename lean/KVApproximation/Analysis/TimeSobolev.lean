module

public import TauCeti.Analysis.Sobolev.EvolutionSpace.Basic

/-!
# Hilbert-valued H¹ trajectories on a finite time interval
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1: `H¹((0,T);H)`. The identity pivot records a derivative
in the Hilbert dual of `H`, which the Riesz isometry identifies with `H`. -/
abbrev TimeH1 (T : ℝ) :=
  TauCeti.EvolutionSpace (ContinuousLinearMap.id ℝ H) 0 T

variable {H}

/-- Theorem 3.1: the `H`-valued representative of a finite-time trajectory. -/
def TimeH1.value {T : ℝ} (u : TimeH1 H T) (t : ℝ) : H :=
  TauCeti.EvolutionSpace.value u t

/-- Theorem 3.1: the `H`-valued weak time derivative, obtained from the
dual-valued derivative using the inverse Riesz isometry. -/
def TimeH1.velocity {T : ℝ} (u : TimeH1 H T) (t : ℝ) : H :=
  (InnerProductSpace.toDual ℝ H).symm (TauCeti.EvolutionSpace.timeDeriv u t)

/-- Theorem 3.1: the continuous trace, including both endpoints. -/
def TimeH1.trace {T : ℝ} (hT : 0 < T) (u : TimeH1 H T) :
    C(Set.Icc (0 : ℝ) T, H) :=
  TauCeti.EvolutionSpace.toContinuousMap hT u

/-- Theorem 3.1: evaluation of the continuous representative at time zero. -/
def TimeH1.initial {T : ℝ} (hT : 0 < T) (u : TimeH1 H T) : H :=
  TimeH1.trace (H := H) hT u ⟨0, le_rfl, hT.le⟩

end KVApproximation.Analysis
