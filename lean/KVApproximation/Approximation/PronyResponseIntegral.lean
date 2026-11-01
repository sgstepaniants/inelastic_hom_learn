module

public import KVApproximation.Approximation.PartitionResponseContinuity
public import KVApproximation.Approximation.PronyModels
public import KVApproximation.Approximation.RealResponseIdentities
public import KVApproximation.Spectral.TensorActionIntegration

/-!
# Signed coefficient assembly for the Prony stress
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10, coefficient assembly: the finite Prony stress is
the instantaneous response plus the integrated partitioned interpolant. -/
theorem local_prony_stress_eq_partitionIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {c lower upper : ℝ} (hlower : 0 < lower) (hc : 0 < c) (m : ℕ) (a : M)
    (hνpos : (ν a).Positive) (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (localPronyModel ν Vhom Ehom c lower upper m).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (weightedMeasure c (ν a))
          (partitionResponse c lower upper m e t) := by
  let μ := weightedMeasure c (ν a)
  let R := logarithmicSpan lower upper
  let rate := localPronyRate lower upper m
  let coeff := localPronyCoefficient (ν a) c lower upper m
  let w (j : Fin (logPartitionCount R)) (i : Fin m) (r : ℝ) :=
    spectralWeight lower upper j r * (chebyshevLagrange m i).eval (localCoordinate lower R j r)
  let W (j : Fin (logPartitionCount R)) (i : Fin m) := realWeightedResponse c e t (rate j i)
  obtain ⟨_, _, hsupport, hvar⟩ :=
    weightedMeasure_properties hlower hc (ν a) hνpos hνsupport hνfinite
  have hwi (j : Fin (logPartitionCount R)) (i : Fin m) : Integrable (w j i) μ.variation :=
    μ.integrable_continuousOn (hvar.trans_lt hνfinite) hsupport _
      (continuousOn_localPronyWeight hlower m j i)
  have hgi (j : Fin (logPartitionCount R)) (i : Fin m) :
      Integrable (fun r => w j i r • W j i) μ.variation := (hwi j i).smul_const (W j i)
  have hterm (j : Fin (logPartitionCount R)) (i : Fin m) :
      tensorActionIntegral μ (fun r => w j i r • W j i) =
        action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    rw [tensorActionIntegral_smul μ _ (hwi j i)]
    change actionL d (tensorIntegral μ (w j i))
      ((c + rate j i) • dampedResponse (rate j i) e.velocity t) =
      actionL d ((c + rate j i) • tensorIntegral μ (w j i))
        (dampedResponse (rate j i) e.velocity t)
    simp only [map_smul, smul_apply]
  have hpartition : partitionResponse c lower upper m e t =
      fun r => ∑ j, ∑ i, w j i r • W j i := by
    funext r
    simp only [partitionResponse, realLocalResponseInterpolant, Finset.smul_sum, smul_smul]
    rfl
  have hint : tensorActionIntegral μ (partitionResponse c lower upper m e t) =
      ∑ j, ∑ i, action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    rw [hpartition]
    calc
      _ = ∑ j, tensorActionIntegral μ (fun r => ∑ i, w j i r • W j i) :=
        VectorMeasure.integral_finsetSum _ (fun j _ =>
          integrable_finsetSum _ (fun i _ => hgi j i))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show tensorActionIntegral μ (fun r => ∑ i, w j i r • W j i) =
            ∑ i, tensorActionIntegral μ (fun r => w j i r • W j i) from
          VectorMeasure.integral_finsetSum _ (fun i _ => hgi j i)]
        exact Finset.sum_congr rfl (fun i _ => hterm j i)
  have hstate (j : Fin (logPartitionCount R)) (i : Fin m) :
      (∫ s in (0 : ℝ)..t, Real.exp (-rate j i * (t - s)) •
        actionL d (coeff j i) (e.velocity s)) =
      action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    have hi : IntervalIntegrable
        (fun s => Real.exp (-rate j i * (t - s)) • e.velocity s) volume 0 t :=
      (e.velocity_intervalIntegrable le_rfl ht).continuousOn_smul (by fun_prop)
    simpa only [map_smul, actionL_apply, dampedResponse] using
      (actionL d (coeff j i)).intervalIntegral_comp_comm hi
  rw [hint]
  unfold PronyModel.stress PronyModel.stressResponse PronyModel.state localPronyModel
  congr 1
  change (∑ k, ∫ s in (0 : ℝ)..t,
    Real.exp (-rate (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 * (t - s)) •
      actionL d (coeff (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) (e.velocity s)) = _
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun ji => ∫ s in (0 : ℝ)..t, Real.exp (-rate ji.1 ji.2 * (t - s)) •
      actionL d (coeff ji.1 ji.2) (e.velocity s)) (fun _ => rfl), Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hstate j i))

end KVApproximation.Approximation
