module

public import KVApproximation.Approximation.GlobalResponse
public import KVApproximation.Approximation.RealResponseIdentities
public import KVApproximation.Spectral.TensorActionIntegration
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The global Prony stress as an integral
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Remark 4.6: the global Prony coefficients assemble the weighted interpolant. -/
theorem global_prony_stress_eq_responseIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {c lower upper : ℝ} (hlower : 0 < lower) (hc : 0 < c) (n : ℕ) (a : M)
    (hνpos : (ν a).Positive) (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (globalPronyModel ν Vhom Ehom c lower upper n).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (weightedMeasure c (ν a))
          (globalResponseInterpolant c lower upper n e t) := by
  let μ := weightedMeasure c (ν a)
  let rate (i : Fin n) := globalLogRate lower upper (chebyshevNode n i)
  let coeff := globalPronyCoefficient (ν a) c lower upper n
  let w (i : Fin n) (r : ℝ) := (chebyshevLagrange n i).eval (globalLogCoordinate lower upper r)
  let W (i : Fin n) := realWeightedResponse c e t (rate i)
  obtain ⟨_, _, hsupport, hvar⟩ :=
    weightedMeasure_properties hlower hc (ν a) hνpos hνsupport hνfinite
  have hcoord : ContinuousOn (globalLogCoordinate lower upper) (Set.Icc lower upper) := by
    intro r hr
    have hlog : ContinuousAt (fun r : ℝ => Real.log (r / lower)) r :=
      (continuousAt_id.div_const lower).log (div_pos (hlower.trans_le hr.1) hlower).ne'
    exact (((continuousAt_const.mul hlog).div_const _).sub continuousAt_const).continuousWithinAt
  have hwi (i : Fin n) : Integrable (w i) μ.variation :=
    μ.integrable_continuousOn (hvar.trans_lt hνfinite) hsupport _
      ((chebyshevLagrange n i).continuous.continuousOn.comp hcoord (Set.mapsTo_univ _ _))
  have hgi (i : Fin n) : Integrable (fun r => w i r • W i) μ.variation :=
    (hwi i).smul_const (W i)
  have hterm (i : Fin n) : tensorActionIntegral μ (fun r => w i r • W i) =
      action (coeff i) (dampedResponse (rate i) e.velocity t) := by
    rw [tensorActionIntegral_smul μ _ (hwi i)]
    change actionL d (tensorIntegral μ (w i)) ((c + rate i) • dampedResponse (rate i) e.velocity t) =
      actionL d ((c + rate i) • tensorIntegral μ (w i)) (dampedResponse (rate i) e.velocity t)
    simp only [map_smul, smul_apply]
  have hint : tensorActionIntegral μ (globalResponseInterpolant c lower upper n e t) =
      ∑ i, action (coeff i) (dampedResponse (rate i) e.velocity t) := by
    change tensorActionIntegral μ (fun r => ∑ i, w i r • W i) = _
    rw [show tensorActionIntegral μ (fun r => ∑ i, w i r • W i) =
        ∑ i, tensorActionIntegral μ (fun r => w i r • W i) from
      VectorMeasure.integral_finsetSum _ (fun i _ => hgi i)]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hstate (i : Fin n) :
      (∫ s in (0 : ℝ)..t, Real.exp (-rate i * (t - s)) • actionL d (coeff i) (e.velocity s)) =
      action (coeff i) (dampedResponse (rate i) e.velocity t) := by
    have hi : IntervalIntegrable (fun s => Real.exp (-rate i * (t - s)) • e.velocity s)
        volume 0 t := (e.velocity_intervalIntegrable le_rfl ht).continuousOn_smul (by fun_prop)
    simpa only [map_smul, actionL_apply, dampedResponse] using
      (actionL d (coeff i)).intervalIntegral_comp_comm hi
  rw [hint]
  unfold PronyModel.stress PronyModel.stressResponse PronyModel.state globalPronyModel
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hstate i)

end KVApproximation.Approximation
