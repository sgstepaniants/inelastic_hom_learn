module

public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# Uniform spectral discretization of the constitutive law
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Spectral
open KVApproximation.Approximation KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Definition B.8: all local rates belong to the common spectral interval. -/
theorem localPronyRate_mem {lower upper : ℝ} (hlower : 0 < lower) (horder : lower < upper)
    {m : ℕ} (hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) :
    localPronyRate lower upper m j i ∈ Set.Icc lower upper := by
  sorry

/-- Definition B.8 (`eq:Kn_def`): flattening the local indices preserves
the exact tensor-valued kernel. -/
theorem localPronyModel_kernel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (c lower upper : ℝ) (m : ℕ) (a : M) (t : ℝ) :
    (localPronyModel ν Vhom Ehom c lower upper m).kernel a t =
      actionL d (localPronyKernel (ν a) c lower upper m t) := by
  sorry

end KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Proposition B.10 (`eq:prony_homogenized_error_uniform`): the strict
uniform error bound is taken after both material and strain supremums. -/
theorem local_prony_error_lt (hd : 0 < d) (hδ : 0 < δ)
    (hspan : αE / βV < βE / αV) {m : ℕ} (hm : 0 < m) :
    uniformPronyError C
      (localPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
        (βE / βV) (αE / βV) (βE / αV) m) δ <
      ENNReal.ofReal (pronyErrorBound (strainDimension d) δ m) := by
  sorry

/-- Proposition B.10 (`eq:Ki_def_degenerate`): the singleton construction
reproduces the constitutive stress exactly at every nonnegative time. -/
theorem singleton_prony_exact (hspan : αE / βV = βE / αV)
    (M : admissibleMaterials d αV βV γV αE βE γE)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    constitutiveStress (C M) e t =
      (singletonPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (αE / βV)).stress M e t := by
  sorry

variable (M : admissibleMaterials d αV βV γV αE βE γE)
variable (Mseq : ℕ → admissibleMaterials d αV βV γV αE βE γE)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y) 1 (cellMeasure d)) atTop (𝓝 0))

include hVconv hEconv

/-- Proposition B.10, coefficient continuity: L¹ convergence of admissible
materials gives convergence of every signed local coefficient. -/
theorem local_prony_coefficient_converges
    (hspan : αE / βV < βE / αV) {m : ℕ} (hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)))) (i : Fin m) :
    Tendsto (fun n => localPronyCoefficient (S.measure (Mseq n))
        (βE / βV) (αE / βV) (βE / αV) m j i)
      atTop (𝓝 (localPronyCoefficient (S.measure M) (βE / βV) (αE / βV) (βE / αV) m j i)) := by
  sorry

/-- Proposition B.10, singleton coefficient continuity: the first spectral
moment is continuous under L¹ convergence of admissible materials. -/
theorem singleton_prony_coefficient_converges (hspan : αE / βV = βE / αV) :
    Tendsto (fun n => singletonPronyCoefficient (S.measure (Mseq n)))
      atTop (𝓝 (singletonPronyCoefficient (S.measure M))) := by
  sorry

end KVApproximation.KelvinVoigt
