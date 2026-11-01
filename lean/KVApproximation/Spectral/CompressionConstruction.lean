module

public import KVApproximation.Spectral.Compression
public import KVApproximation.Spectral.FiniteCompression
public import KVApproximation.Spectral.ContinuousCalculus
public import KVApproximation.OperatorTheory.SpectralBounds

/-!
# The compressed relaxation measure

The real embedding of the viscous Hilbert space into its complexification is
isometric. Composing it with mismatch gives the compression map for the cell
spectral measure. Its positive trace controls variation, and the relaxation
spectrum supplies its support.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.OperatorTheory KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2: mismatch followed by the real embedding in the Hilbert complexification. -/
private def complexMismatchL {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : Symmetric d →L[ℝ] H) : Symmetric d →L[ℝ] ComplexRelaxationSpace V X :=
  LinearMap.mkContinuous
    { toFun := complexMismatch V E X ι
      map_add' e f := by
        unfold complexMismatch
        rw [map_add, ← WithLp.toLp_add]
        congr 1
        simpa only [TauCeti.Complexification.ofRealLI_apply] using
          (TauCeti.Complexification.ofRealLI (RelaxationSpace V X)).map_add
            (weightedMismatch V E X ι e) (weightedMismatch V E X ι f)
      map_smul' r e := by
        unfold complexMismatch
        rw [map_smul, ← WithLp.toLp_smul]
        congr 1
        simpa only [TauCeti.Complexification.ofRealLI_apply, RingHom.id_apply] using
          (TauCeti.Complexification.ofRealLI (RelaxationSpace V X)).map_smul r
            (weightedMismatch V E X ι e) }
    ‖weightedMismatch V E X ι‖ (fun e => by
      change ‖complexMismatch V E X ι e‖ ≤ ‖weightedMismatch V E X ι‖ * ‖e‖
      rw [complexMismatch, WithLp.complexification_norm_toLp_ofReal]
      exact (weightedMismatch V E X ι).le_opNorm e)

/-- Appendix A.2 (`eq:nu_def`): strong PVM additivity and finite-dimensional
tensor representation construct the unique compressed tensor measure. -/
theorem compressedMeasure_exists_unique {d : ℕ} (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : Symmetric d →L[ℝ] H) :
    ∃! ν : TensorMeasure d, IsCompressedMeasure V E X ι ν :=
  pvmCompression_exists_unique (relaxationPVM V E X) (complexMismatchL V E X ι)

/-- Appendix A.2: compression is positive and its trace is the sum of
the mismatch energies on any orthonormal basis. -/
theorem compressedMeasure_positive_trace {d : ℕ} (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : IsCompressedMeasure V E X ι ν) {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ ℝ (Symmetric d)) :
    ν.Positive ∧
      tensorTrace (ν Set.univ) = ∑ i, ‖weightedMismatch V E X ι (b i)‖ ^ 2 ∧
      totalVariation ν Set.univ ≤
        ENNReal.ofReal (∑ i, ‖weightedMismatch V E X ι (b i)‖ ^ 2) := by
  have h := pvmCompression_positive_trace (relaxationPVM V E X)
    (complexMismatchL V E X ι) ν hν b
  have hnorm (e : Symmetric d) :
      ‖complexMismatchL V E X ι e‖ = ‖weightedMismatch V E X ι e‖ :=
    WithLp.complexification_norm_toLp_ofReal _
  simpa only [hnorm] using h

variable {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
  (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
  (hν : IsCompressedMeasure V E X ι ν)
  {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
  (hαE : 0 < αE) (hβE : 0 < βE)
  (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)

include hν hαV hβV hαE hβE hV hE

/-- Appendix A.2: the compressed measure inherits the spectral interval
and is finite in the physical Frobenius norm. -/
theorem compressedMeasure_supported :
    ν.SupportedOn (Set.Icc (αE / βV) (βE / αV)) ∧
      totalVariation ν Set.univ < ⊤ := by
  have hP := (boundedPVM_supported
    (ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff.mpr
      (weightedRelaxation_isSelfAdjoint V E X))
    (weightedRelaxation_complex_spectrum_subset V E X hαV hβV hαE hβE hV hE)).2
  have hzero : ν (Set.Icc (αE / βV) (βE / αV))ᶜ = 0 := by
    apply eq_of_inner_action_eq
    intro e f
    rw [hν _ measurableSet_Icc.compl]
    change (⟪(TauCeti.BorelCalculus.boundedPVM _).proj _ _
      (complexMismatch V E X ι e), complexMismatch V E X ι f⟫_ℂ).re =
      ⟪e, (actionL d 0) f⟫_ℝ
    rw [hP]
    simp
  obtain ⟨hpos, _, hvar⟩ := compressedMeasure_positive_trace V E X ι ν hν
    (stdOrthonormalBasis ℝ (Symmetric d))
  constructor
  · change totalVariation ν (Set.Icc (αE / βV) (βE / αV))ᶜ = 0
    apply le_antisymm _ bot_le
    calc
      _ ≤ ENNReal.ofReal (tensorTrace (ν (Set.Icc (αE / βV) (βE / αV))ᶜ)) :=
        ν.variation_le_trace hpos measurableSet_Icc.compl
      _ = 0 := by rw [hzero]; simp [tensorTrace]
  · exact hvar.trans_lt ENNReal.ofReal_lt_top

end KVApproximation.Spectral
