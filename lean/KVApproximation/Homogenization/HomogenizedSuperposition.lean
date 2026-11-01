module

public import KVApproximation.Homogenization.HomogenizedMemory
import Lean.Elab.Tactic

/-!
# Superposition for the homogenized weak equation
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, superposition: add the Sobolev representatives and the
causal memory integral on one common full-measure time set. -/
private theorem timeH1_memory_add
    {H Y Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (hT : 0 < T) (V E : H →L[ℝ] Y) (L : Z →L[ℝ] H →L[ℝ] Y)
    (K : ℝ → Z) (hK : Continuous K) (u v : TimeH1 H T) (a b : ℝ → Y)
    (hu : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = a t)
    (hv : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity v t) + E (TimeH1.value v t) +
        posConvolution K (TimeH1.velocity v) L volume t = b t) :
    TimeH1.initial hT (u + v) = TimeH1.initial hT u + TimeH1.initial hT v ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        V (TimeH1.velocity (u + v) t) + E (TimeH1.value (u + v) t) +
          posConvolution K (TimeH1.velocity (u + v)) L volume t = a t + b t := by
  have hvalue : TimeH1.value (u + v) =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => TimeH1.value u t + TimeH1.value v t := by
    filter_upwards [Lp.coeFn_add (TauCeti.EvolutionSpace.value u)
      (TauCeti.EvolutionSpace.value v)] with t ht
    change TauCeti.EvolutionSpace.value (u + v) t = _
    rw [TauCeti.EvolutionSpace.value_add]
    exact ht
  have hvelocity : TimeH1.velocity (u + v) =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => TimeH1.velocity u t + TimeH1.velocity v t := by
    filter_upwards [Lp.coeFn_add (TauCeti.EvolutionSpace.timeDeriv u)
      (TauCeti.EvolutionSpace.timeDeriv v)] with t ht
    simp only [Pi.add_apply] at ht
    simp only [TimeH1.velocity, TauCeti.EvolutionSpace.timeDeriv_add, ht, map_add]
  have huvel : IntervalIntegrable (TimeH1.velocity u) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((TimeH1.velocity_memLp u).integrable (by norm_num))
  have hvvel : IntervalIntegrable (TimeH1.velocity v) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((TimeH1.velocity_memLp v).integrable (by norm_num))
  have hmemory (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      posConvolution K (TimeH1.velocity (u + v)) L volume t =
        posConvolution K (TimeH1.velocity u) L volume t +
          posConvolution K (TimeH1.velocity v) L volume t := by
    rw [posConvolution_eq_integral_sub L K _ ht.1,
      posConvolution_eq_integral_sub L K _ ht.1,
      posConvolution_eq_integral_sub L K _ ht.1]
    calc
      _ = ∫ r in (0 : ℝ)..t,
          (L (K (t - r)) (TimeH1.velocity u r) + L (K (t - r)) (TimeH1.velocity v r)) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [Set.uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
        have heq := ae_restrict_of_ae_restrict_of_subset
          (Set.Ioo_subset_Ioo le_rfl ht.2) hvelocity
        filter_upwards [heq] with r hr
        rw [hr, (L (K (t - r))).map_add]
      _ = _ := intervalIntegral.integral_add
        (intervalIntegrable_posConvolution_integrand L K (TimeH1.velocity u) hK huvel ht)
        (intervalIntegrable_posConvolution_integrand L K (TimeH1.velocity v) hK hvvel ht)
  constructor
  · exact congrArg (fun w : C(Set.Icc (0 : ℝ) T, H) => w ⟨0, le_rfl, hT.le⟩)
      ((TauCeti.EvolutionSpace.toContinuousMap
        (ι := ContinuousLinearMap.id ℝ H) hT).map_add u v)
  · filter_upwards [hu, hv, hvalue, hvelocity, ae_restrict_mem measurableSet_Ioo]
      with t htu htv hval hvel ht
    calc
      _ = (V (TimeH1.velocity u t) + V (TimeH1.velocity v t)) +
          (E (TimeH1.value u t) + E (TimeH1.value v t)) +
          (posConvolution K (TimeH1.velocity u) L volume t +
            posConvolution K (TimeH1.velocity v) L volume t) :=
        congrArg₂ (· + ·)
          (congrArg₂ (· + ·) ((congrArg V hvel).trans (V.map_add _ _))
            ((congrArg E hval).trans (E.map_add _ _))) (hmemory t ⟨ht.1.le, ht.2.le⟩)
      _ = (V (TimeH1.velocity u t) + E (TimeH1.value u t) +
          posConvolution K (TimeH1.velocity u) L volume t) +
          (V (TimeH1.velocity v t) + E (TimeH1.value v t) +
          posConvolution K (TimeH1.velocity v) L volume t) := by abel
      _ = _ := congrArg₂ (· + ·) htu htv

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedSuperposition.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedSuperposition.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), superposition:
adding the homogeneous and forced solutions adds their prepared initial
loads and their L² forcing in the actual weak memory equation. -/
theorem IsHomogenizedSolution.add {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ g₁ : SpatialL2 Ω) (f₀ f₁ : Forcing Ω T)
    (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K g₀ f₀ u)
    (hv : IsHomogenizedSolution hT Vhom Ehom K g₁ f₁ v) :
    IsHomogenizedSolution hT Vhom Ehom K (g₀ + g₁) (f₀ + f₁) (u + v) := by
  have hu' := (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK g₀ f₀ u).mp hu
  have hv' := (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK g₁ f₁ v).mp hv
  have hsum := timeH1_memory_add hT (constantSpatialFormL (Ω := Ω) Vhom)
    (constantSpatialFormL (Ω := Ω) Ehom) (constantSpatialFormL (Ω := Ω)) K hK u v
    (fun t => spatialLoadOperator (Ω := Ω) (f₀ t))
    (fun t => spatialLoadOperator (Ω := Ω) (f₁ t)) hu'.2 hv'.2
  apply (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK
    (g₀ + g₁) (f₀ + f₁) (u + v)).mpr
  constructor
  · exact (congrArg (constantSpatialFormL (Ω := Ω) Ehom) hsum.1).trans
      (((constantSpatialFormL (Ω := Ω) Ehom).map_add _ _).trans
        ((congrArg₂ (· + ·) hu'.1 hv'.1).trans
          ((spatialLoadOperator (Ω := Ω)).map_add g₀ g₁).symm))
  · filter_upwards [hsum.2, Lp.coeFn_add f₀ f₁] with t ht hforce
    exact ht.trans (((spatialLoadOperator (Ω := Ω)).map_add (f₀ t) (f₁ t)).symm.trans
      (congrArg (spatialLoadOperator (Ω := Ω)) hforce.symm))

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel assembly:
the forced equation for a trajectory difference and the homogeneous
equation recover the equation with the original initial load and forcing. -/
theorem IsHomogenizedSolution.of_sub {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g : SpatialL2 Ω) (f : Forcing Ω T)
    (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K 0 f (u - v))
    (hv : IsHomogenizedSolution hT Vhom Ehom K g 0 v) :
    IsHomogenizedSolution hT Vhom Ehom K g f u := by
  -- Reuse the typed arguments to avoid repeatedly elaborating the Sobolev structures.
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let hu := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hu))
      let hv := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hv))
      let hK := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hK))
      let tu ← Lean.Meta.inferType hu
      let tv ← Lean.Meta.inferType hv
      let au := tu.getAppArgs
      let av := tv.getAppArgs
      unless tu.getAppFn.isConstOf `KVApproximation.Homogenization.IsHomogenizedSolution &&
          tv.getAppFn.isConstOf `KVApproximation.Homogenization.IsHomogenizedSolution &&
          au.size == 10 && av.size == 10 do
        throwError "Expected two homogenized solution proofs"
      let proof := Lean.mkAppN
        (Lean.mkConst `KVApproximation.Homogenization.IsHomogenizedSolution.add)
        ((au.extract 0 7) ++ #[hK, au[7]!, av[7]!, au[8]!, av[8]!, au[9]!, av[9]!, hu, hv])
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hsum proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  have hg : (0 : SpatialL2 Ω) + g = g := @zero_add (SpatialL2 Ω) inferInstance g
  have hf : f + (0 : Forcing Ω T) = f := @add_zero (Forcing Ω T) inferInstance f
  have huv : (u - v) + v = u :=
    @sub_add_cancel (TimeH1 (ZeroBoundaryH1 Ω) T) inferInstance u v
  have hdata := congrArg₂
    (fun a b => @IsHomogenizedSolution d Ω T hT Vhom Ehom K a b ((u - v) + v)) hg hf
  have htrajectory := congrArg (@IsHomogenizedSolution d Ω T hT Vhom Ehom K g f) huv
  exact Eq.mp (hdata.trans htrajectory) hsum

end KVApproximation.Homogenization
