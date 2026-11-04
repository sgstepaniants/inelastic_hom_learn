import KVApproximation.KelvinVoigt.Homogenization
import KVApproximation.KelvinVoigt.SpectralRepresentation
import KVApproximation.KelvinVoigt.UniversalApproximation
import KVApproximation.KelvinVoigt.SpectralEdgeDiscontinuity

/-!
# Main results

The five main results in manuscript order, with parameters and hypotheses on
each declaration. Each proof invokes the corresponding theorem in its subject
module, where the detailed proof is retained.

* Theorem 3.1: `viscoelastic_homogenization`
* Proposition 3.3: `spectral_representation`
* Theorem 4.4: `universal_approximation`
* Theorem 4.5: `sufficient_internal_variable_dimension`
* Proposition 4.7: `spectral_edge_discontinuous`

The reader's guide links the project definitions used in these statements.
-/

open Filter MeasureTheory TopologicalSpace
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization
open KVApproximation.Spectral KVApproximation.NeuralOperators KVApproximation.KelvinVoigt

namespace KVApproximation.MainResults

/-!
## Theorem 3.1: periodic viscoelastic homogenization
-/

/-- Existence and uniqueness of the microscopic and homogenized solutions,
with weak convergence of the whole positive-scale family in H¹(0,T;H¹₀(Ω;ℝᵈ)). -/
theorem viscoelastic_homogenization {d : ℕ}
    (hd : d ∈ ({1, 2, 3} : Set ℕ))
    (Ω : Opens (PhysicalSpace d))
    (hΩbounded : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (hΩlipschitz : HasLipschitzBoundary (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (V E : CoerciveField d)
    (g₀ : SpatialL2 Ω) (u₀ : ℝ → ZeroBoundaryH1 Ω)
    (hprepared : IsPreparedInitialFamily E g₀ u₀) (f : Forcing Ω T) :
    ∃ C : CellConstitutiveModel V E,
      PositiveDefinite C.viscosity ∧ PositiveDefinite C.elasticity ∧
      Continuous C.kernel ∧
      (∀ t : ℝ, 0 ≤ t → ∀ e : Symmetric d,
        0 ≤ ⟪e, action (C.kernel t) e⟫_ℝ) ∧
      ∃ (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
        (uHom : TimeH1 (ZeroBoundaryH1 Ω) T),
        (∀ ε : ℝ, 0 < ε →
          IsMicroscopicSolution hT V E ε (u₀ ε) f (u ε) ∧
          ∀ v : TimeH1 (ZeroBoundaryH1 Ω) T,
            IsMicroscopicSolution hT V E ε (u₀ ε) f v → v = u ε) ∧
        IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uHom ∧
        (∀ v : TimeH1 (ZeroBoundaryH1 Ω) T,
          IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f v → v = uHom) ∧
        ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
          Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ uHom)) := by
  exact KVApproximation.Homogenization.viscoelastic_homogenization
    hd Ω hΩbounded hΩlipschitz hT V E g₀ u₀ hprepared f

/-!
## Proposition 3.3: spectral representation
-/

/-- A positive tensor measure represents the cell memory kernel, with the stated
spectral support and Frobenius total-variation bound. -/
theorem spectral_representation {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field) :
    ∃ ν : TensorMeasure d,
      ν.Positive ∧
      ν.SupportedOn (Set.Icc (lowerRate αE βV) (upperRate βE αV)) ∧
      totalVariation ν Set.univ ≤
        ENNReal.ofReal (spectralVariationBound (strainDimension d) βV βE αE) ∧
      ∀ t : ℝ, 0 ≤ t →
        C.kernel t = tensorIntegral ν (fun r => r * Real.exp (-r * t)) := by
  exact KVApproximation.Spectral.spectral_representation
    V E C hαV hβV hαE hβE hV hE

/-!
## Theorem 4.4: uniform approximation
-/

/-- Under A1/A2, finite-dimensional internal-variable models approximate the
response uniformly over the material and strain classes on nonnegative time. -/
theorem universal_approximation {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 3)
    {αV βV γV αE βE γE δ : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
    (Fclass : ∀ nξ : ℕ, StressResponseClass d nξ)
    (Gclass : ∀ nξ : ℕ, KineticResponseClass d nξ)
    (hF : ∀ nξ, HasUniversalApproximation (Fclass nξ))
    (hG : ∀ nξ, HasLocallyLipschitzApproximation (Gclass nξ)) :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε → ∃ nξ : ℕ,
        ∃ F ∈ Fclass nξ, ∃ G ∈ Gclass nξ,
          UniformlyApproximates C F G δ ε := by
  exact KVApproximation.KelvinVoigt.universal_approximation
    hd hαV hVorder hγV hαE hEorder hγE hδ Fclass Gclass hF hG

/-!
## Theorem 4.5: sufficient internal-variable dimension
-/

/-- The sufficient scalar state dimension is determined by the common spectral
interval and relative error ε / δ, including the singleton-spectrum case. -/
theorem sufficient_internal_variable_dimension {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 3)
    {αV βV γV αE βE γE δ : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
    (Fclass : ∀ nξ : ℕ, StressResponseClass d nξ)
    (Gclass : ∀ nξ : ℕ, KineticResponseClass d nξ)
    (hF : ∀ nξ, HasUniversalApproximation (Fclass nξ))
    (hG : ∀ nξ, HasLocallyLipschitzApproximation (Gclass nξ)) :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let N := sufficientDimension d
          (Approximation.logarithmicSpan (αE / βV) (βE / αV)) (ε / δ)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  exact KVApproximation.KelvinVoigt.sufficient_internal_variable_dimension
    hd hαV hVorder hγV hαE hEorder hγE hδ Fclass Gclass hF hG

/-!
## Proposition 4.7: spectral-edge discontinuity
-/

/-- A thin-strip family in one BV-bounded material class converges in L¹ and L²
while its upper spectral edge remains two and the limit has upper edge one. -/
theorem spectral_edge_discontinuous {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (i : Fin d) :
    ∃ γV γE : ℝ, 0 < γV ∧ 0 < γE ∧
      ∃ M : admissibleMaterials d 1 1 γV 1 2 γE,
      ∃ Mseq : ℕ → admissibleMaterials d 1 1 γV 1 2 γE,
        (∀ᵐ y ∂cellMeasure d, M.val.1 y = identityElasticity d ∧
          M.val.2 y = identityElasticity d) ∧
        (∀ n, ∀ᵐ y ∂cellMeasure d,
          (Mseq n).val.1 y = identityElasticity d ∧
            (Mseq n).val.2 y = stripElasticity i n y) ∧
        Tendsto (fun n => (Mseq n).val) atTop (𝓝 M.val) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        materialSpectralEdge (by norm_num) (by norm_num) M = 1 ∧
        (∀ n, materialSpectralEdge (by norm_num) (by norm_num) (Mseq n) = 2) ∧
        ¬ Continuous (materialSpectralEdge (d := d) (γV := γV) (γE := γE)
          (βV := 1) (βE := 2) (show (0 : ℝ) < 1 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)) := by
  exact KVApproximation.KelvinVoigt.spectral_edge_discontinuous hd i

end KVApproximation.MainResults
