module

public import KVApproximation.Analysis.PeriodicSmooth
public import KVApproximation.Tensor.Symmetrization
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Periodic displacement Sobolev spaces

The value-gradient pairs are completed in their full Hilbert norm.
The distributional characterization and Korn estimate identify the corrector range.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1: a displacement and its full gradient, with their
Euclidean product norm. -/
abbrev PeriodicJet (d : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin d) × SecondOrder d)

/-- Section 3.1: square-integrable value-gradient pairs on the unit cell. -/
abbrev PeriodicJetField (d : ℕ) := Lp (PeriodicJet d) 2 (cellMeasure d)

/-- Section 3.1: the gradient of a periodic displacement, evaluated
on coordinate unit vectors in physical space. -/
def periodicGradient {d : ℕ}
    (φ : PeriodicCell d → EuclideanSpace ℝ (Fin d)) (y : PeriodicCell d) :
    SecondOrder d :=
  WithLp.toLp 2 (fun ij =>
    (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => φ (toCell x))
      (cellRepresentative y) (WithLp.toLp 2 (Pi.single ij.2 (1 : ℝ)))) ij.1)

/-- Section 3.1: smooth periodic displacement jets. -/
def smoothPeriodicJets (d : ℕ) : Set (PeriodicJetField d) :=
  {u | ∃ φ : PeriodicCell d → EuclideanSpace ℝ (Fin d),
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => φ (toCell x)) ∧
      ∀ᵐ y ∂cellMeasure d, u y = WithLp.toLp 2 (φ y, periodicGradient φ y)}

/-- Section 3.1: the full periodic H¹ space, as the closure of smooth
periodic jets in the value-gradient norm. -/
def periodicH1Submodule (d : ℕ) : ClosedSubmodule ℝ (PeriodicJetField d) :=
  (Submodule.span ℝ (smoothPeriodicJets d)).closure

/-- Section 3.1: `H¹_per(𝕋ᵈ;ℝᵈ)`. -/
abbrev PeriodicH1 (d : ℕ) := (periodicH1Submodule d).toSubmodule

instance (d : ℕ) : InnerProductSpace ℝ (PeriodicH1 d) :=
  Submodule.innerProductSpace (𝕜 := ℝ) (E := PeriodicJetField d)
    (periodicH1Submodule d).toSubmodule

instance (d : ℕ) : CompleteSpace (PeriodicH1 d) :=
  (periodicH1Submodule d).isClosed.completeSpace_coe

/-- Section 3.1: the displacement component of a periodic H¹ field. -/
def PeriodicH1.valueL (d : ℕ) :
    PeriodicH1 d →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d) :=
  ((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
    2 (cellMeasure d)).comp (periodicH1Submodule d).toSubmodule.subtypeL

/-- Section 3.1: the full gradient component of a periodic H¹ field. -/
def PeriodicH1.gradientL (d : ℕ) :
    PeriodicH1 d →L[ℝ] Lp (SecondOrder d) 2 (cellMeasure d) :=
  ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
    2 (cellMeasure d)).comp (periodicH1Submodule d).toSubmodule.subtypeL

/-- Section 3.1 (`eq:space_strain_corrector`): the symmetric gradient. -/
def PeriodicH1.symmetricGradientL (d : ℕ) :
    PeriodicH1 d →L[ℝ] Lp (Symmetric d) 2 (cellMeasure d) :=
  ((symmetrizeL d).compLpL 2 (cellMeasure d)).comp (PeriodicH1.gradientL d)

/-- Section 3.1: integration of a periodic L² displacement over the
normalized unit cell, expressed as a Hölder pairing with the constant one. -/
def cellAverageL (d : ℕ) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).lpPairing
    (cellMeasure d) 2 2 (Lp.const 2 (cellMeasure d) (1 : ℝ))

/-- Section 3.1: the closed subspace of periodic H¹ displacements with zero mean. -/
def zeroMeanPeriodicSubmodule (d : ℕ) : ClosedSubmodule ℝ (PeriodicH1 d) :=
  (⊥ : ClosedSubmodule ℝ (EuclideanSpace ℝ (Fin d))).comap
    ((cellAverageL d).comp (PeriodicH1.valueL d))

/-- Section 3.1: the zero-mean displacement-corrector space. -/
abbrev ZeroMeanPeriodicH1 (d : ℕ) := (zeroMeanPeriodicSubmodule d).toSubmodule

instance (d : ℕ) : InnerProductSpace ℝ (ZeroMeanPeriodicH1 d) :=
  Submodule.innerProductSpace (𝕜 := ℝ) (E := PeriodicH1 d)
    (zeroMeanPeriodicSubmodule d).toSubmodule

instance (d : ℕ) : CompleteSpace (ZeroMeanPeriodicH1 d) :=
  (zeroMeanPeriodicSubmodule d).isClosed.completeSpace_coe

/-- Section 3.1 (`eq:space_strain_corrector`): the symmetric-gradient
map on zero-mean periodic displacements. -/
def correctorGradientL (d : ℕ) :
    ZeroMeanPeriodicH1 d →L[ℝ] Lp (Symmetric d) 2 (cellMeasure d) :=
  (PeriodicH1.symmetricGradientL d).comp
    (zeroMeanPeriodicSubmodule d).toSubmodule.subtypeL

/-- Section 3.1: the distributional identity for a periodic weak gradient,
tested against every scalar C¹ periodic function. -/
def HasPeriodicWeakGradient {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) : Prop :=
  ∀ (φ : PeriodicC1 d ℝ) (i j : Fin d),
    (∫ y, u y i * φ.partial j y ∂cellMeasure d) =
      -(∫ y, g y (i, j) * φ.value y ∂cellMeasure d)

end KVApproximation.Analysis
