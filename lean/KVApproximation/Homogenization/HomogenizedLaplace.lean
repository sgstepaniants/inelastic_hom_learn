module

public import KVApproximation.Homogenization.StaticHomogenization
public import KVApproximation.Homogenization.MicroscopicLaplace
public import KVApproximation.Homogenization.RescaledFieldCombinations
public import KVApproximation.Tensor.FieldCombinations

/-!
# Effective equations for prepared Laplace limits

Static homogenization identifies the transformed velocity for elastically
prepared data and the displacement transform for viscously prepared data.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, transformed velocity: weak convergence is preserved
by a fixed scalar multiple and subtraction of the initial state. -/
private theorem weak_smul_sub_tendsto {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p q : ℕ → H) (pLim qLim : H) (s : ℝ)
    (hp : ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun n => ℓ (p n)) atTop (𝓝 (ℓ pLim)))
    (hq : ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ qLim))) :
    ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (s • p n - q n)) atTop (𝓝 (ℓ (s • pLim - qLim))) := by
  intro ℓ
  simpa only [map_sub, map_smul, smul_eq_mul] using ((hp ℓ).const_mul s).sub (hq ℓ)

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedLaplace.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedLaplace.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, transformed loads: scalar multiplication acts on the
actual L² load class before its continuous dual pairing. -/
private theorem loadPairing_smul (c : ℝ) (g : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    loadPairing (c • g) v = c * loadPairing g v := by
  rw [← spatialLoadOperator_apply, map_smul, smul_apply,
    smul_eq_mul, spatialLoadOperator_apply]

/-- Theorem 3.1, elastic preparation in the Laplace-domain limit:
the transformed velocity solves the effective combined-coefficient
equation with load -g/s. -/
theorem prepared_laplace_equilibrium (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field (ε n)) (q n) v = loadPairing g v)
    (qLim L : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s)
    (hqWeak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ qLim)))
    (hLap : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω)
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
        atTop (𝓝 (ℓ L))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
          (symmetricGradient (s • L - qLim) x) (symmetricGradient v x)) =
            -s⁻¹ * loadPairing g v := by
  let Ln (n : ℕ) : ZeroBoundaryH1 Ω := halfLineLaplace (F := ZeroBoundaryH1 Ω)
    (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s
  let A := V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)
  have hEq (n : ℕ) (v : ZeroBoundaryH1 Ω) :
      spatialForm (rescalePeriodic A.field (ε n)) (s • Ln n - q n) v =
        loadPairing ((-s⁻¹) • g) v := by
    change spatialForm (rescalePeriodic (V.field + s⁻¹ • E.field) (ε n))
      (s • Ln n - q n) v = _
    rw [spatialForm_rescalePeriodic_add_smul V.field E.field s⁻¹ (ε n) (hpos n).ne',
      loadPairing_smul]
    exact microscopic_prepared_laplace_form (Ω := Ω) V E hΩ (ε n) (hpos n).ne'
      (q n) g (hq n) hs v
  have hWeak (ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ) :
      Tendsto (fun n => ℓ (s • Ln n - q n)) atTop (𝓝 (ℓ (s • L - qLim))) :=
    weak_smul_sub_tendsto Ln q L qLim s hLap hqWeak ℓ
  have hlimit := periodic_elliptic_weak_limit A hΩ ((-s⁻¹) • g) ε hε hpos
    (fun n => s • Ln n - q n) hEq (s • L - qLim) hWeak
  intro v
  exact (hlimit v).trans (loadPairing_smul (-s⁻¹) g v)

/-- Theorem 3.1, viscous preparation in the Duhamel argument:
the displacement transform solves the effective combined-coefficient
equation with load g/s. -/
theorem viscous_laplace_equilibrium (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field (ε n)) (q n) v = loadPairing g v)
    (L : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s)
    (hLap : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω)
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
        atTop (𝓝 (ℓ L))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
          (symmetricGradient L x) (symmetricGradient v x)) =
            s⁻¹ * loadPairing g v := by
  let Ln (n : ℕ) : ZeroBoundaryH1 Ω := halfLineLaplace (F := ZeroBoundaryH1 Ω)
    (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s
  let A := V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)
  have hEq (n : ℕ) (v : ZeroBoundaryH1 Ω) :
      spatialForm (rescalePeriodic A.field (ε n)) (Ln n) v =
        loadPairing (s⁻¹ • g) v := by
    change spatialForm (rescalePeriodic (V.field + s⁻¹ • E.field) (ε n)) (Ln n) v = _
    rw [spatialForm_rescalePeriodic_add_smul V.field E.field s⁻¹ (ε n) (hpos n).ne',
      loadPairing_smul]
    exact microscopic_viscous_laplace_form (Ω := Ω) V E hΩ (ε n) (hpos n).ne'
      (q n) g (hq n) hs v
  have hlimit := periodic_elliptic_weak_limit A hΩ (s⁻¹ • g) ε hε hpos Ln hEq L hLap
  intro v
  exact (hlimit v).trans (loadPairing_smul s⁻¹ g v)

end KVApproximation.Homogenization
