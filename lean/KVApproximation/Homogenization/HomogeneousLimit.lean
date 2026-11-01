module

public import KVApproximation.Homogenization.HomogenizedMemory
public import KVApproximation.Homogenization.HomogenizedLaplace
public import KVApproximation.Homogenization.TransformedCell
public import KVApproximation.Analysis.TimeSobolevLaplaceMemory

/-!
# Identification of homogeneous microscopic limits

Static homogenization identifies the initial state and transformed velocity.
The cell identity and Laplace injectivity then recover the weak memory PDE.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogeneousLimit.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogeneousLimit.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1, transformed spatial equation: coefficient linearity
transfers the cell identity to the spatial operator before integration. -/
private theorem combinedSpatialForm_apply
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    {s : ℝ} (hs : 0 < s) (z w : ZeroBoundaryH1 Ω) :
    (constantSpatialFormL (Ω := Ω) C.viscosity +
      s⁻¹ • constantSpatialFormL (Ω := Ω) C.elasticity +
      constantSpatialFormL (Ω := Ω) (halfLineLaplace C.kernel s)) z w =
        ∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
            (symmetricGradient z x) (symmetricGradient w x) := by
  have hmap : constantSpatialFormL (Ω := Ω)
      (C.viscosity + s⁻¹ • C.elasticity + halfLineLaplace C.kernel s) =
      constantSpatialFormL (Ω := Ω) C.viscosity +
        s⁻¹ • constantSpatialFormL (Ω := Ω) C.elasticity +
        constantSpatialFormL (Ω := Ω) (halfLineLaplace C.kernel s) := by
    simp only [map_add, map_smul]
  rw [← hmap, constantSpatialFormL_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ⟪symmetricGradient z x,
      actionL d (C.viscosity + s⁻¹ • C.elasticity + halfLineLaplace C.kernel s)
        (symmetricGradient w x)⟫_ℝ = _
    simp only [map_add, map_smul, add_apply, smul_apply, inner_add_right, actionL_apply]
    rw [real_inner_smul_right (symmetricGradient z x)
      (action C.elasticity (symmetricGradient w x)) s⁻¹, C.viscosity_eq, C.elasticity_eq]
    exact (effectiveForm_addSMul_laplace V E C hs
      (symmetricGradient z x) (symmetricGradient w x)).symm

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), identification
of a homogeneous subsequential limit: weak convergence of prepared initial
states and their microscopic Laplace transforms gives the actual homogenized
weak equation with the cell tensors and memory kernel. -/
theorem homogeneous_limit_isHomogenizedSolution
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω) (g₀ : SpatialL2 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field (ε n)) (q n) w = loadPairing g₀ w)
    (u : TimeH1 (ZeroBoundaryH1 Ω) T) (v : ℝ → ZeroBoundaryH1 Ω)
    (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT u t = v t)
    (hqWeak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ (TimeH1.initial hT u))))
    (hLapWeak : ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
          atTop (𝓝 (ℓ (halfLineLaplace v s)))) :
    IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 u := by
  have hinit : constantSpatialFormL (Ω := Ω) C.elasticity (TimeH1.initial hT u) =
      spatialLoadOperator (Ω := Ω) g₀ := by
    apply ContinuousLinearMap.ext
    intro w
    simpa only [constantSpatialFormL_apply, spatialForm, C.elasticity_eq,
      spatialLoadOperator_apply] using
      periodic_elliptic_weak_limit E hΩ g₀ ε hε hpos q hq (TimeH1.initial hT u) hqWeak w
  have hLap (s : ℝ) (hs : 0 < s) :
      (constantSpatialFormL (Ω := Ω) C.viscosity +
        s⁻¹ • constantSpatialFormL (Ω := Ω) C.elasticity +
        constantSpatialFormL (Ω := Ω) (halfLineLaplace C.kernel s))
          (s • halfLineLaplace v s - TimeH1.initial hT u) =
            -s⁻¹ • constantSpatialFormL (Ω := Ω) C.elasticity (TimeH1.initial hT u) := by
    apply ContinuousLinearMap.ext
    intro w
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
            (symmetricGradient (s • halfLineLaplace v s - TimeH1.initial hT u) x)
            (symmetricGradient w x) := combinedSpatialForm_apply V E C hs _ w
      _ = -s⁻¹ * loadPairing g₀ w :=
        prepared_laplace_equilibrium V E hΩ ε hε hpos q g₀ hq
          (TimeH1.initial hT u) (halfLineLaplace v s) hs hqWeak (hLapWeak s hs) w
      _ = _ := by
        rw [hinit, smul_apply, spatialLoadOperator_apply, smul_eq_mul]
  have hmemory : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      constantSpatialFormL (Ω := Ω) C.viscosity (TimeH1.velocity u t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (TimeH1.value u t) +
        posConvolution C.kernel (TimeH1.velocity u) (constantSpatialFormL (Ω := Ω)) volume t = 0 :=
    TimeH1.memory_equation_of_halfLineLaplace hT u v hv hbound htrace
      (constantSpatialFormL (Ω := Ω) C.viscosity) (constantSpatialFormL (Ω := Ω) C.elasticity)
      (constantSpatialFormL (Ω := Ω)) C.kernel (cellKernel_continuous V E C)
      (fun s hs => cellKernel_integrable_halfLineLaplace V E C hs) hLap
  apply (isHomogenizedSolution_iff_memory_equation hT C.viscosity C.elasticity C.kernel
    (cellKernel_continuous V E C) g₀ 0 u).mpr
  refine ⟨hinit, ?_⟩
  filter_upwards [hmemory, Lp.coeFn_zero (SpatialL2 Ω) 2
    (volume.restrict (Set.Ioo 0 T))] with t ht hz
  simpa only [hz, Pi.zero_apply, map_zero] using ht

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel's
homogeneous evolutions: a viscously prepared Laplace limit satisfies the
constant-load Green balance with the actual cell tensors and kernel. -/
theorem viscous_limit_green_balance
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field (ε n)) (q n) w = loadPairing g w)
    (v : ℝ → ZeroBoundaryH1 Ω) (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (hLapWeak : ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
          atTop (𝓝 (ℓ (halfLineLaplace v s)))) :
    ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
        posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g := by
  have hLap (s : ℝ) (hs : 0 < s) :
      (constantSpatialFormL (Ω := Ω) C.viscosity +
        s⁻¹ • constantSpatialFormL (Ω := Ω) C.elasticity +
        constantSpatialFormL (Ω := Ω) (halfLineLaplace C.kernel s))
          (halfLineLaplace v s) = s⁻¹ • spatialLoadOperator (Ω := Ω) g := by
    apply ContinuousLinearMap.ext
    intro w
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
            (symmetricGradient (halfLineLaplace v s) x) (symmetricGradient w x) :=
        combinedSpatialForm_apply V E C hs _ w
      _ = s⁻¹ * loadPairing g w :=
        viscous_laplace_equilibrium V E hΩ ε hε hpos q g hq
          (halfLineLaplace v s) hs (hLapWeak s hs) w
      _ = _ := by rw [smul_apply, spatialLoadOperator_apply, smul_eq_mul]
  exact integrated_memory_eq_const_of_halfLineLaplace
    (constantSpatialFormL (Ω := Ω) C.viscosity) (constantSpatialFormL (Ω := Ω) C.elasticity)
    (constantSpatialFormL (Ω := Ω)) C.kernel (cellKernel_continuous V E C)
    (fun s hs => cellKernel_integrable_halfLineLaplace V E C hs)
    v hv hbound (spatialLoadOperator (Ω := Ω) g) hLap

end KVApproximation.Homogenization
