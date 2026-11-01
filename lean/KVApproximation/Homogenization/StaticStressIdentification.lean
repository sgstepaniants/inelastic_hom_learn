module

public import KVApproximation.Homogenization.StaticCellFluxProperties
public import KVApproximation.Homogenization.SpatialFields
public import KVApproximation.Analysis.PeriodicCorrectorTests
public import KVApproximation.Analysis.PeriodicStressLimits

/-!
# Identification of the microscopic stress limit

Coefficient symmetry equates the two corrected strain pairings. The
oscillating cell flux tends to its mean, while testing equilibrium by
the localized corrector removes the remaining oscillatory term.
-/

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Homogenization

private theorem integrable_cutoff_inner {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (χ : 𝓓(Ω, ℝ)) {a b : PhysicalSpace d → F}
    (ha : MemLp a 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hb : MemLp b 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    Integrable (fun x => χ x * ⟪a x, b x⟫_ℝ)
      (volume.restrict (Ω : Set (PhysicalSpace d))) := by
  have hi : Integrable (fun x => ⟪a x, b x⟫_ℝ)
      (volume.restrict (Ω : Set (PhysicalSpace d))) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (ha.toLp a) (hb.toLp b)).congr
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy]
  exact hi.mul_of_top_right (TauCeti.memLp_testFunction (mu := volume) ⊤ χ)

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, static periodic homogenization: the two oscillating
tests identify every localized constant-strain pairing of the microscopic
stress with the actual effective cell form. -/
theorem tendsto_integral_cutoff_microscopic_stress {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (f : SpatialL2 Ω)
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    {u : ι → ZeroBoundaryH1 Ω} {u₀ : ZeroBoundaryH1 Ω}
    (hu : Tendsto (fun i => VectorH1.valueL Ω (u i).val) l
      (𝓝 (VectorH1.valueL Ω u₀.val)))
    (σ : ι → Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖σ i‖ ≤ C)
    (hσ : ∀ᶠ i in l, σ i =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      action (rescalePeriodic A.field (ε i) x) (VectorH1.symmetricGradientL Ω (u i).val x))
    (heq : ∀ᶠ i in l, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ i x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = loadPairing f v)
    (χ : 𝓓(Ω, ℝ)) (e : Symmetric d) :
    Tendsto (fun i => ∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪σ i x, e⟫_ℝ) l
      (𝓝 (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * effectiveForm A (VectorH1.symmetricGradientL Ω u₀.val x) e)) := by
  obtain ⟨w, hw, _⟩ := exists_unique_static_corrector A e
  let η : StrainField d := cellProjection A (constantStrainL d e)
  have hw' : PeriodicH1.symmetricGradientL d w.val = -η := hw
  have hw_ae : PeriodicH1.symmetricGradientL d w.val =ᵐ[cellMeasure d]
      fun y => -η y := by
    rw [hw']
    exact Lp.coeFn_neg η
  have hflux : cellFlux A e =ᵐ[cellMeasure d] fun y =>
      action (A.field y) (e + PeriodicH1.symmetricGradientL d w.val y) := by
    filter_upwards [cellFlux_apply_ae A e, hw_ae] with y hy hw_y
    rw [hy, hw_y]
    rfl
  have heq' : ∀ᶠ i in l, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ i x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) =
          ⟪f, VectorH1.valueL Ω v.val⟫_ℝ := by
    filter_upwards [heq] with i hi
    intro v
    rw [hi v, loadPairing_eq_inner]
  have hcorrector := tendsto_integral_cutoff_stress_corrector_zero_along
    hΩ χ w.val f hε σ hC hbound heq'
  have hcell := tendsto_integral_cutoff_rescale_stress_strain_along
    (cellFlux A e) (cellFlux_orthogonal_periodic A e) hΩ χ hε hu
  have hmean :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪∫ y, cellFlux A e y ∂cellMeasure d,
          VectorH1.symmetricGradientL Ω u₀.val x⟫_ℝ) =
      ∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * effectiveForm A (VectorH1.symmetricGradientL Ω u₀.val x) e := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrArg (χ x * ·) (by
      calc
        _ = ⟪VectorH1.symmetricGradientL Ω u₀.val x,
            ∫ y, cellFlux A e y ∂cellMeasure d⟫_ℝ := real_inner_comm _ _
        _ = _ := cellFlux_mean_pairing A _ e)
  rw [hmean] at hcell
  have hlim := hcell.sub hcorrector
  simp only [sub_zero] at hlim
  apply hlim.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with r hr hr₁
    exact ⟨hr, hr₁.le⟩
  filter_upwards [hε.eventually hsmall, hσ] with i hi hσi
  have hfluxi : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      rescalePeriodic (cellFlux A e) (ε i) x =
        action (rescalePeriodic A.field (ε i) x)
          (e + rescalePeriodic (PeriodicH1.symmetricGradientL d w.val) (ε i) x) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hi.1.ne').ae hflux)
  have hint₁ := integrable_cutoff_inner χ
    (memLp_two_rescalePeriodic hΩ hi.1 hi.2 (Lp.memLp (cellFlux A e)))
    (Lp.memLp (VectorH1.symmetricGradientL Ω (u i).val))
  have hint₂ := integrable_cutoff_inner χ (Lp.memLp (σ i))
    (memLp_two_rescalePeriodic hΩ hi.1 hi.2
      (Lp.memLp (PeriodicH1.symmetricGradientL d w.val)))
  rw [← integral_sub hint₁ hint₂]
  apply integral_congr_ae
  filter_upwards [hfluxi, hσi] with x hx hs
  rw [hx, hs]
  have hid (B : Elasticity d) (g q : Symmetric d) :
      ⟪action B (e + q), g⟫_ℝ = ⟪action B g, e⟫_ℝ + ⟪action B g, q⟫_ℝ := by
    calc
      _ = ⟪e + q, action B g⟫_ℝ := action_symmetric B _ _
      _ = ⟪action B g, e + q⟫_ℝ := real_inner_comm _ _
      _ = _ := inner_add_right _ _ _
  rw [hid]
  ring

end KVApproximation.Homogenization
