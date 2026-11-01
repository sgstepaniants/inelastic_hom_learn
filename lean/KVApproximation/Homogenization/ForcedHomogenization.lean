module

public import KVApproximation.Homogenization.HomogeneousConvergence
public import KVApproximation.Homogenization.MicroscopicSolutionFamily
public import KVApproximation.Homogenization.HomogenizedGreen
public import KVApproximation.Homogenization.DuhamelLimit
public import KVApproximation.Homogenization.ForcedSubsequence
import Lean.Elab.Tactic

/-!
# Homogenization with general forcing

Duhamel convergence identifies the trace of every bounded microscopic
subsequence. Its difference from the homogeneous limit is an actual Sobolev
realization of the Green convolution. The forced memory equation and
superposition identify the limit, and uniqueness gives whole-family convergence.
-/

set_option Elab.async false

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, Duhamel assembly: weak convergence of the homogeneous
trace and its forced correction gives the full weak trace limit. -/
private theorem weak_trace_of_difference
    {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {l : Filter I} {T : ℝ} (hT : 0 < T)
    (u v : I → TimeH1 H T) (vLim : TimeH1 H T) (q : Set.Icc (0 : ℝ) T → H)
    (hv : ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (v i)) l (𝓝 (ℓ vLim)))
    (hdiff : ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (TimeH1.trace hT (u i) t - TimeH1.trace hT (v i) t))
        l (𝓝 (ℓ (q t)))) :
    ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (TimeH1.trace hT (u i) t))
        l (𝓝 (ℓ (q t + TimeH1.trace hT vLim t))) := by
  intro t ℓ
  simpa only [map_sub, map_add, sub_add_cancel] using
    (hdiff t ℓ).add (TimeH1.weak_trace_tendsto hT v vLim hv t ℓ)

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ForcedHomogenization.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ForcedHomogenization.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), general forcing:
the whole microscopic family with elastically prepared initial data and
L² forcing converges weakly in H¹(0,T;H¹₀) to the unique solution with the
actual cell tensors and memory kernel. -/
theorem forced_homogenization
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω)
    (q : ℝ → ZeroBoundaryH1 Ω) (hq : IsPreparedInitialFamily E g₀ q)
    (f : Forcing Ω T) (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) f (u ε)) :
    ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uLim ∧
      (∀ w : TimeH1 (ZeroBoundaryH1 Ω) T,
        IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f w → w = uLim) ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ uLim)) := by
  classical
  have hvFamily := @exists_microscopic_solution_family d Ω V E hΩ T hT q 0
  let v := hvFamily.choose
  have hv := hvFamily.choose_spec
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let names := #[`d, `Ω, `V, `E, `C, `hΩ, `T, `hT, `g₀, `q, `hq, `v, `hv]
      let args ← names.mapM fun name => do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let theoremName := ``homogeneous_homogenization
      let info ← Lean.getConstInfo theoremName
      unless info.levelParams.isEmpty && info.type.getForallArity == 13 do
        throwError "Expected the thirteen-argument homogeneous convergence theorem"
      let proof := Lean.mkAppN (Lean.mkConst theoremName) args
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hHomLimit proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  let uHom := hHomLimit.choose
  have hHomProps := hHomLimit.choose_spec
  have hHom := hHomProps.1
  have hHomWeak := hHomProps.2.2
  have hGreenExists := @exists_homogenizedGreen d Ω V E C hΩ
  let M := hGreenExists.choose
  have hM := hGreenExists.choose_spec.1
  have hGExists := hGreenExists.choose_spec.2
  let G := hGExists.choose
  have hGprops := hGExists.choose_spec
  have hG := hGprops.1
  have hGbound := hGprops.2.1
  have hGLip := hGprops.2.2.1
  have hbalance := hGprops.2.2.2.1
  have hGreenWeak := hGprops.2.2.2.2
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let names := #[`d, `Ω, `V, `E, `hΩ, `T, `hT, `f, `q, `u, `v,
        `hu, `hv, `G, `hG, `hGreenWeak]
      let args ← names.mapM fun name => do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let theoremName := ``microscopic_forcing_trace_tendsto
      let info ← Lean.getConstInfo theoremName
      unless info.levelParams.isEmpty && info.type.getForallArity == 18 do
        throwError "Expected sixteen Duhamel data arguments and two weak-trace tests"
      let proof := Lean.mkAppN (Lean.mkConst theoremName) args
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hdiff proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  let qDiff : Set.Icc (0 : ℝ) T → ZeroBoundaryH1 Ω :=
    fun t => ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let localArg (name : Lean.Name) := do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let hdiff ← localArg `hdiff
      let diffType ← Lean.instantiateMVars (← Lean.Meta.inferType hdiff)
      let some trace := diffType.find? (fun e =>
          e.getAppFn.isConstOf ``TimeH1.trace && e.getAppArgs.size == 7) |
        throwError "Expected the actual Sobolev trace in the Duhamel limit"
      let some limit := diffType.find? (fun e =>
          e.getAppFn.isConstOf ``Filter.Tendsto && e.getAppArgs.size == 5) |
        throwError "Expected the weak Duhamel limit"
      let a := trace.getAppArgs
      let b := limit.getAppArgs
      unless ((a.extract 0 6) ++ #[b[0]!, b[3]!]).all (fun e => !e.hasLooseBVars) do
        throwError "Trace parameters and the scale filter must be independent of the tests"
      for carrier in #[b[0]!, a[0]!] do
        unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType carrier)
            (Lean.mkSort (.succ .zero)) do
          throwError "Expected real scales and the spatial Hilbert carrier in Type"
      let u ← localArg `u
      let v ← localArg `v
      let uHom ← localArg `uHom
      let qDiff ← localArg `qDiff
      let hHomWeak ← localArg `hHomWeak
      let theoremName := ``weak_trace_of_difference
      let info ← Lean.getConstInfo theoremName
      unless info.type.getForallArity == 16 do
        throwError "Expected the fourteen trace-sum arguments and two result tests"
      let proof := Lean.mkAppN (Lean.mkConst theoremName (info.levelParams.map fun _ => .zero))
        (#[b[0]!] ++ (a.extract 0 4) ++
          #[b[3]!, a[4]!, a[5]!, u, v, uHom, qDiff, hHomWeak, hdiff])
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `htrace proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  have htime := exists_uniform_prepared_timeH1_bound (Ω := Ω) V E hΩ hT
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖u ε‖ ≤ htime.choose * (‖g₀‖ + ‖f‖) :=
    htime.choose_spec.2 g₀ q hq ε hε f (u ε) (hu ε hε)
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let names := #[`d, `Ω, `V, `E, `C, `T, `hT, `g₀, `f,
        `uHom, `hHom, `G, `hG, `hbalance]
      let args ← names.mapM fun name => do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let theoremName := ``forced_subsequence_of_trace
      let info ← Lean.getConstInfo theoremName
      unless info.levelParams.isEmpty && info.type.getForallArity == 18 do
        throwError "Expected the eighteen-argument forced subsequence theorem"
      let proof := Lean.mkAppN (Lean.mkConst theoremName) args
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hSubProducer proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  have hsub (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
      (hpos : ∀ n, 0 < ε n) :
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
        IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uLim ∧
        ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u (ε (φ n)))) atTop (𝓝 (ℓ uLim)) := by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let localArg (name : Lean.Name) := do
          return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
        let producer ← localArg `hSubProducer
        let u ← localArg `u
        let ε ← localArg `ε
        let hε ← localArg `hε
        let hpos ← localArg `hpos
        let hbound ← localArg `hbound
        let htrace ← localArg `htrace
        let boundType ← Lean.instantiateMVars (← Lean.Meta.inferType hbound)
        let bound ← Lean.Meta.forallTelescope boundType fun xs body => do
          let body := body.consumeMData
          unless xs.size == 2 && body.getAppFn.consumeMData.isConstOf ``LE.le &&
              body.getAppArgs.size == 4 do
            throwError "Expected the actual positive-scale uniform norm bound"
          let bound := body.getAppArgs[3]!
          if (bound.find? fun e => xs.contains e).isSome || bound.hasLooseBVars then
            throwError "The uniform bound must be independent of the scale and positivity proof"
          return bound
        let (sequence, sequenceBound) ←
          Lean.Meta.withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
            let scaled := Lean.mkApp ε n
            let sequence ← Lean.Meta.mkLambdaFVars #[n] (Lean.mkApp u scaled)
            let sequenceBound ← Lean.Meta.mkLambdaFVars #[n]
              (Lean.mkAppN hbound #[scaled, Lean.mkApp hpos n])
            return (sequence, sequenceBound)
        let traceType ← Lean.instantiateMVars (← Lean.Meta.inferType htrace)
        let sequenceTrace ← Lean.Meta.forallTelescope traceType fun xs _ => do
          unless xs.size == 2 do
            throwError "Expected the two weak-trace tests"
          let composed ← Lean.Meta.mkAppM ``Filter.Tendsto.comp
            #[Lean.mkAppN htrace xs, hε]
          Lean.Meta.mkLambdaFVars xs composed
        let proof := Lean.mkAppN producer #[sequence, bound, sequenceBound, sequenceTrace]
        let _ ← Lean.Meta.inferType proof
        Lean.Elab.Tactic.closeMainGoal `forcedFamilySubsequence proof
  have hV : PositiveDefinite C.viscosity := by
    refine ⟨V.lower, V.lower_pos, fun e => ?_⟩
    rw [C.viscosity_eq]
    exact (effectiveForm_bounds V V.lower_pos V.bounds e).1
  have hE : PositiveDefinite C.elasticity := by
    refine ⟨E.lower, E.lower_pos, fun e => ?_⟩
    rw [C.elasticity_eq]
    exact (effectiveForm_bounds E E.lower_pos E.bounds e).1
  exact exists_test_limit_of_unique_subsequences
    (X := TimeH1 (ZeroBoundaryH1 Ω) T)
    (fun (ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ)
      (v : TimeH1 (ZeroBoundaryH1 Ω) T) => ℓ v)
    (fun w => IsHomogenizedSolution (Ω := Ω) (T := T) hT
      C.viscosity C.elasticity C.kernel g₀ f w) u hsub
    (fun v w hv hw => @homogenized_solution_unique d Ω hΩ T hT
      C.viscosity C.elasticity hV hE C.kernel (cellKernel_continuous V E C)
      g₀ f v w hv hw)

end KVApproximation.Homogenization
