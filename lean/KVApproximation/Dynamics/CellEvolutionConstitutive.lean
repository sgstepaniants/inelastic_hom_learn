module

public import KVApproximation.Dynamics.CellEvolutionDuhamel
public import KVApproximation.OperatorTheory.MemoryIdentities

/-!
# The cell evolution and the constitutive memory law
-/

public section

open MeasureTheory Set
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3 and Remark 3.2: the direct cell derivation yields the same
instantaneous tensors and memory convolution as the homogenization theorem. -/
theorem cell_evolution_constitutive_law (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 F T) (η : TimeH1 X T)
    (hη : IsCellEvolution V E X ι hT e η) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ a : F,
      cellStressPairing V E X ι e η t a =
        V.homogenizedForm X ι a (TimeH1.velocity e t) +
          E.homogenizedForm X ι a (TimeH1.value e t) +
            ∫ s in (0 : ℝ)..t, memoryForm V E X ι (t - s) a (TimeH1.velocity e s) := by
  have hrem := cell_evolution_stress_remainder V E X ι hT e η hη
  let D := (mismatch V E X).comp ι
  have hD : IntegrableOn (fun s => D (TimeH1.velocity e s)) (Ioo 0 T) :=
    ((TimeH1.velocity_memLp e).continuousLinearMap_comp D).integrable (by norm_num)
  filter_upwards [hrem, TimeH1.trace_ae hT η, TimeH1.trace_ae hT e,
    ae_restrict_mem measurableSet_Ioo] with t hremt hηt het ht
  intro a
  have htT : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hω : TimeH1.value (H := X) η t + E.projection X (ι (TimeH1.value e t)) =
      -(∫ s in (0 : ℝ)..t, relaxationSemigroup V E X (t - s) (D (TimeH1.velocity e s))) := by
    rw [hηt, het, projIcc_of_mem hT.le htT]
    exact cell_evolution_duhamel V E X ι hT e η hη ⟨t, htT⟩
  have hDi : IntervalIntegrable (fun s => D (TimeH1.velocity e s)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).2
      (hD.mono_set (Ioo_subset_Ioo le_rfl ht.2.le))
  have hSi : IntervalIntegrable
      (fun s => relaxationSemigroup V E X (t - s) (D (TimeH1.velocity e s)))
      volume 0 t :=
    intervalIntegrable_continuous_clm_apply
      ((relaxationSemigroup_continuous V E X).comp
        (continuous_const.sub continuous_id)).continuousOn hDi
  let B := (V.restrict X).form (relaxation V E X (D a))
  have hr := hremt a
  change cellStressPairing V E X ι e η t a =
    V.homogenizedForm X ι a (TimeH1.velocity e t) +
      E.homogenizedForm X ι a (TimeH1.value e t) -
        B (TimeH1.value (H := X) η t + E.projection X (ι (TimeH1.value e t))) at hr
  rw [hω, map_neg, sub_neg_eq_add] at hr
  rw [hr]
  congr 1
  rw [← B.intervalIntegral_comp_comm hSi]
  apply intervalIntegral.integral_congr
  intro s _
  change V.form (relaxation V E X (D a))
    (relaxationSemigroup V E X (t - s) (D (TimeH1.velocity e s))) =
      V.form (relaxation V E X (relaxationSemigroup V E X (t - s) (D a)))
        (D (TimeH1.velocity e s))
  rw [← relaxationSemigroup_selfAdjoint]
  have hc := congrArg (fun S : X →L[ℝ] X => S (D a))
    (relaxationSemigroup_commute V E X (t - s))
  change relaxation V E X (relaxationSemigroup V E X (t - s) (D a)) =
    relaxationSemigroup V E X (t - s) (relaxation V E X (D a)) at hc
  rw [← hc]

end KVApproximation.Dynamics
