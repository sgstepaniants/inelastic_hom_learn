module

public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.Dynamics.PronyConvolution

/-!
# Exact Prony representation of a singleton spectrum
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics
open KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Proposition B.10 (`eq:Ki_def_degenerate`): the singleton construction
reproduces the constitutive stress exactly at every nonnegative time. -/
theorem singleton_prony_exact (hspan : αE / βV = βE / αV)
    (M : admissibleMaterials d αV βV γV αE βE γE)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    constitutiveStress (C M) e t =
      (singletonPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (αE / βV)).stress M e t := by
  have hsupport := (S.represents M).2.1
  rw [← hspan] at hsupport
  have hae : ∀ᵐ r ∂(S.measure M).variation, r = αE / βV :=
    (ae_iff.mpr hsupport).mono fun _ hr => le_antisymm hr.2 hr.1
  have hkernel (u : ℝ) (hu : 0 ≤ u) :
      actionL d ((C M).kernel u) =
        (singletonPronyModel S.measure (fun M => (C M).viscosity)
          (fun M => (C M).elasticity) (αE / βV)).kernel M u := by
    have htensor : (C M).kernel u =
        Real.exp (-(αE / βV) * u) • singletonPronyCoefficient (S.measure M) := by
      rw [(S.represents M).2.2.2 u hu]
      unfold singletonPronyCoefficient tensorIntegral
      rw [← VectorMeasure.integral_fun_smul]
      apply VectorMeasure.integral_congr_ae
      filter_upwards [hae] with r hr
      rw [hr]
      exact mul_comm _ _
    rw [htensor]
    simp only [PronyModel.kernel, singletonPronyModel, Fin.sum_univ_one, map_smul]
  rw [pronyStress_eq_kernel_convolution _ M e ht]
  change action (C M).viscosity (e.velocity t) + action (C M).elasticity (e.value t) +
      (∫ s in (0 : ℝ)..t, action ((C M).kernel (t - s)) (e.velocity s)) =
    action (C M).viscosity (e.velocity t) + action (C M).elasticity (e.value t) + _
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact congrArg (fun L : Symmetric d →L[ℝ] Symmetric d => L (e.velocity s))
    (hkernel (t - s) (sub_nonneg.mpr hs.2))

end KVApproximation.KelvinVoigt
