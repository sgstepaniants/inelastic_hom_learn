module

public import KVApproximation.OperatorTheory.WeightedRelaxation
public import KVApproximation.Spectral.TensorMeasure
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# Compression of the relaxation spectral measure
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.OperatorTheory KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2: Hilbert complexification of the viscous corrector space. -/
abbrev ComplexRelaxationSpace (V : CoerciveForm H) (X : ClosedSubmodule ℝ H) :=
  WithLp 2 (TauCeti.Complexification (RelaxationSpace V X))

/-- Appendix A.2: the canonical bounded PVM of the complexified weighted relaxation operator. -/
def relaxationPVM (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    TauCeti.ProjValMeasure (ComplexRelaxationSpace V X) :=
  TauCeti.BorelCalculus.boundedPVM
    (ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff.mpr
      (weightedRelaxation_isSelfAdjoint V E X))

/-- Appendix A.2: the real mismatch vector embedded in the Hilbert complexification. -/
def complexMismatch {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) (e : F) :
    ComplexRelaxationSpace V X :=
  WithLp.toLp 2 (TauCeti.Complexification.ofReal (weightedMismatch V E X ι e))

/-- Appendix A.2 (`eq:nu_def`): the tensor measure is the real compression
of the canonical PVM through the mismatch, with the paper's pairing order. -/
def IsCompressedMeasure {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d) : Prop :=
  ∀ (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d),
    ⟪e, action (ν B) f⟫_ℝ =
      (⟪(relaxationPVM V E X).proj B hB (complexMismatch V E X ι e),
        complexMismatch V E X ι f⟫_ℂ).re

end KVApproximation.Spectral
