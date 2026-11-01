module

public import KVApproximation.Homogenization.ForcedMemory
public import KVApproximation.Homogenization.HomogenizedSuperposition
public import KVApproximation.Homogenization.CellConstitutive
public import KVApproximation.Analysis.TimeSobolevTraceCompactness
import Lean.Elab.Tactic

/-!
# Identification of forced Sobolev subsequences

A uniform Sobolev bound and a prescribed Green-convolution trace give a weak
subsequential limit satisfying the actual homogenized memory equation.
-/

set_option Elab.async false

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, forced Sobolev realization: subtraction of actual
Sobolev trajectories subtracts their continuous traces at every endpoint. -/
private theorem trace_sub_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (u v : TimeH1 H T) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT (u - v) t = TimeH1.trace hT u t - TimeH1.trace hT v t :=
  congrArg (fun w : C(Set.Icc (0 : ℝ) T, H) => w t)
    ((TauCeti.EvolutionSpace.toContinuousMap
      (ι := ContinuousLinearMap.id ℝ H) hT).map_sub u v)

/-- Theorem 3.1, forced trace: the Green convolution added to a prescribed
homogeneous trace, with the original Bochner integral on each finite interval. -/
private abbrev forcing_trace_sum
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {T : ℝ}
    (G : ℝ → F →L[ℝ] H) (f : ℝ → F) (v : Set.Icc (0 : ℝ) T → H) :
    Set.Icc (0 : ℝ) T → H := fun t =>
  (∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) + v t

/-- Theorem 3.1, subsequence identification: retain the selected index map
and convergence while applying an equation-identification implication. -/
private theorem identify_subsequence {X I : Type*}
    {B Q P : X → Prop} {S : I → Prop} {W : I → X → Prop}
    (hex : ∃ v, B v ∧ Q v ∧ ∃ i, S i ∧ W i v)
    (identify : ∀ v, Q v → P v) : ∃ i, S i ∧ ∃ v, P v ∧ W i v := by
  obtain ⟨v, _, hv, i, hi, hweak⟩ := hex
  exact ⟨i, hi, v, identify v hv, hweak⟩

/-- Theorem 3.1, compactness and identification: an equation determined by
the prescribed trace holds for the actual weak Sobolev subsequential limit. -/
private theorem subsequence_of_trace_identification
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (u : ℕ → TimeH1 H T) {B : ℝ}
    (hbound : ∀ n, ‖u n‖ ≤ B) (q : Set.Icc (0 : ℝ) T → H)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (TimeH1.trace hT (u n) t)) atTop (𝓝 (ℓ (q t))))
    (P : TimeH1 H T → Prop)
    (identify : ∀ v, (∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT v t = q t) → P v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : TimeH1 H T, P v ∧
      ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ v)) := by
  exact identify_subsequence
    (X := TimeH1 H T) (I := ℕ → ℕ)
    (B := fun v => ‖v‖ ≤ B)
    (Q := fun v => ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace (H := H) hT v t = q t)
    (P := P) (S := StrictMono)
    (W := fun φ v => ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ v)))
    (TimeH1.exists_weak_subsequence_with_trace (H := H) (T := T) (C := B)
      hT u hbound q htrace) identify

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ForcedSubsequence.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ForcedSubsequence.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1, identification of forced limits: an actual Sobolev
trajectory with the prescribed Duhamel trace satisfies the full memory PDE. -/
private theorem forced_limit_of_trace
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω) (f : Forcing Ω T)
    (uHom : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hHom : IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 uHom)
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hbalance : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (G t g) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution C.kernel (fun r => G r g)
          (constantSpatialFormL (Ω := Ω)) volume t = spatialLoadOperator (Ω := Ω) g)
    (uLim : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hLimTrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT uLim t =
        (∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) + TimeH1.trace hT uHom t) :
    IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uLim := by
  let uF : TimeH1 (ZeroBoundaryH1 Ω) T := uLim - uHom
  have hFtrace (t : Set.Icc (0 : ℝ) T) :
      TimeH1.trace hT uF t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r) := by
    exact (trace_sub_apply hT uLim uHom t).trans
      ((congrArg (fun x => x - TimeH1.trace hT uHom t) (hLimTrace t)).trans
        (add_sub_cancel_right _ _))
  have hK := cellKernel_continuous V E C
  have hF := @green_trace_isHomogenizedSolution d Ω T hT
    C.viscosity C.elasticity C.kernel hK G hG hbalance f uF hFtrace
  have hFsol := And.right hF
  -- Reuse the typed arguments of the goal and homogeneous equation.
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let originalTarget ← Lean.instantiateMVars (← goal.getType)
      let target := originalTarget.consumeMData
      let hFsol := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hFsol))
      let hHom := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hHom))
      let hK := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hK))
      let homType ← Lean.instantiateMVars (← Lean.Meta.inferType hHom)
      let homType := homType.consumeMData
      let a := target.getAppArgs
      let ah := homType.getAppArgs
      unless target.getAppFn.consumeMData.isConstOf
          `KVApproximation.Homogenization.IsHomogenizedSolution &&
          homType.getAppFn.consumeMData.isConstOf
            `KVApproximation.Homogenization.IsHomogenizedSolution &&
          a.size == 10 && ah.size == 10 do
        throwError "Expected the homogenized solution goal and homogeneous solution proof"
      let proof := Lean.mkAppN
        (Lean.mkConst `KVApproximation.Homogenization.IsHomogenizedSolution.of_sub)
        ((a.extract 0 7) ++ #[hK, a[7]!, a[8]!, a[9]!, ah[9]!, hFsol, hHom])
      let type ← Lean.Meta.inferType proof
      unless ← Lean.Meta.isDefEq type originalTarget do
        throwError "Normalized superposition does not have the required conclusion"
      Lean.Elab.Tactic.closeMainGoal `normalizedSuperposition proof

/-- Theorem 3.1, forced compactness: the prescribed Duhamel trace of an
actual weak H¹ limit identifies its full homogenized memory equation. -/
theorem forced_subsequence_of_trace
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω) (f : Forcing Ω T)
    (uHom : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hHom : IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 uHom)
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hbalance : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (G t g) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution C.kernel (fun r => G r g)
          (constantSpatialFormL (Ω := Ω)) volume t = spatialLoadOperator (Ω := Ω) g)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T) {B : ℝ} (hbound : ∀ n, ‖u n‖ ≤ B)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (TimeH1.trace hT (u n) t)) atTop
        (𝓝 (ℓ ((∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) +
          TimeH1.trace hT uHom t)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uLim ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  let qTrace : Set.Icc (0 : ℝ) T → ZeroBoundaryH1 Ω :=
    forcing_trace_sum (F := SpatialL2 Ω) (H := ZeroBoundaryH1 Ω) (T := T)
      G f (TimeH1.trace (H := ZeroBoundaryH1 Ω) (T := T) hT uHom)
  let P : TimeH1 (ZeroBoundaryH1 Ω) T → Prop :=
    fun (v : TimeH1 (ZeroBoundaryH1 Ω) T) =>
      IsHomogenizedSolution (Ω := Ω) (T := T) hT
        C.viscosity C.elasticity C.kernel g₀ f v
  have hidentify (v : TimeH1 (ZeroBoundaryH1 Ω) T)
      (hv : ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT v t = qTrace t) : P v :=
    @forced_limit_of_trace d Ω V E C T hT g₀ f uHom hHom G hG hbalance v hv
  -- Use the Hilbert structures of the trace hypothesis in the compactness theorem.
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let localArg (name : Lean.Name) := do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let htrace ← localArg `htrace
      let traceType ← Lean.instantiateMVars (← Lean.Meta.inferType htrace)
      let some trace := traceType.find? (fun e =>
          e.getAppFn.isConstOf ``TimeH1.trace && e.getAppArgs.size == 7) |
        throwError "Expected the actual seven-argument Sobolev trace in the trace hypothesis"
      let a := trace.getAppArgs
      unless (a.extract 0 6).all (fun e => !e.hasLooseBVars) do
        throwError "The Sobolev trace parameters must be independent of its bound variables"
      let u ← localArg `u
      let B ← localArg `B
      let hbound ← localArg `hbound
      let qTrace ← localArg `qTrace
      let P ← localArg `P
      let hidentify ← localArg `hidentify
      let helperName := ``subsequence_of_trace_identification
      let helperInfo ← Lean.getConstInfo helperName
      unless helperInfo.levelParams.length == 1 do
        throwError "Expected one Hilbert-space universe parameter"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType a[0]!)
          (Lean.mkSort (.succ .zero)) do
        throwError "Expected the spatial Hilbert carrier in Type"
      let proof := Lean.mkAppN
        (Lean.mkConst helperName [.zero])
        ((a.extract 0 5) ++ #[a[5]!, u, B, hbound, qTrace, htrace, P, hidentify])
      let _ ← Lean.Meta.inferType proof
      Lean.Elab.Tactic.closeMainGoal `forcedSubsequence proof

end KVApproximation.Homogenization
