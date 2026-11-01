module

public import KVApproximation.Homogenization.ForcedHomogenization
public import KVApproximation.Homogenization.CellConstitutive
public import KVApproximation.Homogenization.CellTensorBounds
import Lean.Elab.Tactic

/-!
# Continuum periodic homogenization
-/

set_option Elab.async false

public section

noncomputable section

open Filter TopologicalSpace
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`): the actual periodic
cell forms define the effective tensors and memory kernel. The unique
microscopic solutions converge weakly in `H¹(0,T;H¹₀(Ω;ℝᵈ))` along the whole
positive-scale family. Weak convergence is tested against every continuous
linear functional on that Sobolev space. -/
theorem viscoelastic_homogenization {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
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
  classical
  let C := (cellConstitutiveModel_exists_unique V E).choose
  have hV : PositiveDefinite C.viscosity := by
    refine ⟨V.lower, V.lower_pos, fun e => ?_⟩
    rw [C.viscosity_eq]
    exact (effectiveForm_bounds V V.lower_pos V.bounds e).1
  have hE : PositiveDefinite C.elasticity := by
    refine ⟨E.lower, E.lower_pos, fun e => ?_⟩
    rw [C.elasticity_eq]
    exact (effectiveForm_bounds E E.lower_pos E.bounds e).1
  have hFamily := @exists_microscopic_solution_family d Ω V E hΩbounded T hT u₀ f
  let u := hFamily.choose
  have hu := hFamily.choose_spec
  have hunique (ε : ℝ) (hε : 0 < ε) (v : TimeH1 (ZeroBoundaryH1 Ω) T)
      (hv : IsMicroscopicSolution hT V E ε (u₀ ε) f v) : v = u ε := by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let localArg (name : Lean.Name) := do
          return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
        let args ← #[`d, `Ω, `V, `E, `hΩbounded, `ε, `hε, `T, `hT].mapM localArg
        let u₀ ← localArg `u₀
        let ε ← localArg `ε
        let f ← localArg `f
        let name := ``microscopic_exists_unique
        let info ← Lean.getConstInfo name
        unless info.levelParams.isEmpty && info.type.getForallArity == 11 do
          throwError "Expected the eleven-argument microscopic well-posedness theorem"
        let existsUnique := Lean.mkAppN (Lean.mkConst name)
          (args ++ #[Lean.mkApp u₀ ε, f])
        let existsType ← Lean.instantiateMVars (← Lean.Meta.inferType existsUnique)
        let existsType := existsType.consumeMData
        unless existsType.getAppFn.consumeMData.isConstOf ``ExistsUnique &&
            existsType.getAppArgs.size == 2 do
          throwError "Expected unique existence for the actual microscopic solution"
        let a := existsType.getAppArgs
        let v ← localArg `v
        let u ← localArg `u
        let hv ← localArg `hv
        let hu ← localArg `hu
        let hε ← localArg `hε
        let .const _ levels := existsType.getAppFn.consumeMData |
          throwError "Expected the unique-existence constant and its carrier universe"
        let uniqueName := ``ExistsUnique.unique
        let uniqueInfo ← Lean.getConstInfo uniqueName
        unless uniqueInfo.type.getForallArity == 7 &&
            uniqueInfo.levelParams.length == levels.length do
          throwError "Expected the seven-argument unique-existence elimination theorem"
        let proof := Lean.mkAppN
          (Lean.mkConst uniqueName levels)
          #[a[0]!, a[1]!, existsUnique, v, Lean.mkApp u ε, hv, Lean.mkAppN hu #[ε, hε]]
        let _ ← Lean.Meta.inferType proof
        Lean.Elab.Tactic.closeMainGoal `microscopicUniqueness proof
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let names := #[`d, `Ω, `V, `E, `C, `hΩbounded, `T, `hT,
        `g₀, `u₀, `hprepared, `f, `u, `hu]
      let args ← names.mapM fun name => do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let theoremName := ``forced_homogenization
      let info ← Lean.getConstInfo theoremName
      unless info.levelParams.isEmpty && info.type.getForallArity == 14 do
        throwError "Expected the fourteen-argument general-forcing homogenization theorem"
      let proof := Lean.mkAppN (Lean.mkConst theoremName) args
      let type ← Lean.Meta.inferType proof
      let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hlimit proof (some type)
      Lean.Elab.Tactic.replaceMainGoal [goal]
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let localArg (name : Lean.Name) := do
        return Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent name))
      let splitExists (e : Lean.Expr) :
          Lean.MetaM (List Lean.Level × Lean.Expr × Lean.Expr) := do
        let e := e.consumeMData.headBeta.consumeMData
        unless e.getAppFn.consumeMData.isConstOf ``Exists && e.getAppArgs.size == 2 do
          throwError "Expected an existential in the homogenization conclusion"
        let .const _ levels := e.getAppFn.consumeMData |
          throwError "Expected the existential carrier universe"
        let a := e.getAppArgs
        return (levels, a[0]!, a[1]!)
      let splitAnd (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
        let e := e.consumeMData.headBeta.consumeMData
        unless e.getAppFn.consumeMData.isConstOf ``And && e.getAppArgs.size == 2 do
          throwError "Expected a conjunction in the homogenization conclusion"
        return (e.getAppArgs[0]!, e.getAppArgs[1]!)
      let mkExists (shape : List Lean.Level × Lean.Expr × Lean.Expr)
          (w proof : Lean.Expr) :=
        Lean.mkAppN (Lean.mkConst ``Exists.intro shape.1)
          #[shape.2.1, shape.2.2, w, proof]
      let mkAnd (shape : Lean.Expr × Lean.Expr) (left right : Lean.Expr) :=
        Lean.mkAppN (Lean.mkConst ``And.intro) #[shape.1, shape.2, left, right]
      let C ← localArg `C
      let u ← localArg `u
      let hlimit ← localArg `hlimit
      let hu ← localArg `hu
      let hunique ← localArg `hunique
      let target ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
      let cellShape ← splitExists target
      let mut suffix := (Lean.mkApp cellShape.2.2 C).headBeta
      let mut layers : Array (Lean.Expr × Lean.Expr) := #[]
      for _ in [:4] do
        let layer ← splitAnd suffix
        layers := layers.push layer
        suffix := layer.2
      let familyShape ← splitExists suffix
      let limitShape ← splitExists ((Lean.mkApp familyShape.2.2 u).headBeta)
      let producerShape ← splitExists (← Lean.Meta.inferType hlimit)
      for name in [``Classical.choose, ``Classical.choose_spec] do
        let info ← Lean.getConstInfo name
        unless info.type.getForallArity == 3 &&
            info.levelParams.length == producerShape.1.length do
          throwError "Expected ordinary existential choice and its specification"
      let choiceArgs := #[producerShape.2.1, producerShape.2.2, hlimit]
      let uHom := Lean.mkAppN (Lean.mkConst ``Classical.choose producerShape.1) choiceArgs
      let limitProof := Lean.mkAppN
        (Lean.mkConst ``Classical.choose_spec producerShape.1) choiceArgs
      let solutionShape ← splitAnd ((Lean.mkApp limitShape.2.2 uHom).headBeta)
      let microProof ← Lean.Meta.forallTelescope solutionShape.1 fun xs body => do
        unless xs.size == 2 do
          throwError "Expected positive-scale microscopic solution and uniqueness tests"
        let pair ← splitAnd body
        Lean.Meta.mkLambdaFVars xs
          (mkAnd pair (Lean.mkAppN hu xs) (Lean.mkAppN hunique xs))
      let mut proof := mkExists familyShape u
        (mkExists limitShape uHom (mkAnd solutionShape microProof limitProof))
      let cellArgs ← #[`d, `V, `E, `C].mapM localArg
      let atomProofs := #[← localArg `hV, ← localArg `hE,
        Lean.mkAppN (Lean.mkConst ``cellKernel_continuous) cellArgs,
        Lean.mkAppN (Lean.mkConst ``cellKernel_nonneg) cellArgs]
      for i in [:4] do
        let j := 3 - i
        proof := mkAnd layers[j]! atomProofs[j]! proof
      proof := mkExists cellShape C proof
      let _ ← Lean.Meta.inferType proof
      Lean.Elab.Tactic.closeMainGoal `paperHomogenization proof

end KVApproximation.Homogenization
