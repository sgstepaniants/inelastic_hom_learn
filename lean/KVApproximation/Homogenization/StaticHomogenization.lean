module

public import KVApproximation.Homogenization.StaticEquilibriumLimit
public import KVApproximation.Homogenization.SpatialStress
public import KVApproximation.Homogenization.PeriodicElliptic
public import KVApproximation.Homogenization.EffectiveElliptic
public import KVApproximation.Analysis.DirichletWeakCompactness

/-!
# Static periodic elasticity homogenization

Uniform displacement and stress bounds give compactness along every
sequence of positive scales. Oscillating tests identify each limit with
the unique effective equilibrium, which determines the whole family.
-/

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace Topology

namespace KVApproximation.Homogenization

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, static compactness step: a positive scale sequence
has a weak H¹₀ and strong L² subsequence solving the effective equation. -/
private theorem static_equilibrium_subsequence {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (f : SpatialL2 Ω)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (u : ℕ → ZeroBoundaryH1 Ω)
    (hu : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field (ε n)) (u n) v = loadPairing f v) :
    ∃ uLim : ZeroBoundaryH1 Ω,
      (∀ v : ZeroBoundaryH1 Ω,
        (∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm A (symmetricGradient uLim x) (symmetricGradient v x)) =
            loadPairing f v) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim))) ∧
        Tendsto (fun n => VectorH1.valueL Ω (u (φ n)).val) atTop
          (𝓝 (VectorH1.valueL Ω uLim.val)) := by
  obtain ⟨K, hK, hbound⟩ := periodic_elliptic_uniform_bound A hΩ
  have hubound (n : ℕ) : ‖u n‖ ≤ K * ‖f‖ := hbound (ε n) (hpos n) f (u n) (hu n)
  let σ (n : ℕ) :=
    spatialStressL (rescaledCoefficient Ω A.field (ε n) (hpos n).ne') (u n)
  have hσbound (n : ℕ) : ‖σ n‖ ≤ ‖A.field‖ * (K * ‖f‖) := by
    calc
      _ ≤ ‖rescaledCoefficient Ω A.field (ε n) (hpos n).ne'‖ * ‖u n‖ :=
        norm_spatialStressL_le _ _
      _ ≤ ‖A.field‖ * ‖u n‖ :=
        mul_le_mul_of_nonneg_right
          (norm_rescaledCoefficient_le Ω A.field (ε n) (hpos n).ne') (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hubound n) (norm_nonneg A.field)
  have hσrep (n : ℕ) : σ n =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
      fun x => action (rescalePeriodic A.field (ε n) x)
        (VectorH1.symmetricGradientL Ω (u n).val x) := by
    filter_upwards [spatialStressL_apply_ae
      (rescaledCoefficient Ω A.field (ε n) (hpos n).ne') (u n),
      rescaledCoefficient_apply_ae Ω A.field (ε n) (hpos n).ne'] with x hx hA
    change spatialStressL (rescaledCoefficient Ω A.field (ε n) (hpos n).ne') (u n) x = _
    rw [hx, hA]
  have hσeq (n : ℕ) (v : ZeroBoundaryH1 Ω) :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ n x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = loadPairing f v := by
    change (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪spatialStressL (rescaledCoefficient Ω A.field (ε n) (hpos n).ne') (u n) x,
        VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = _
    rw [integral_spatialStressL_strain, spatialForm_rescaledCoefficient]
    exact hu n v
  obtain ⟨uLim, _, φ, hφ, hweak, hstrong⟩ :=
    ZeroBoundaryH1.exists_subseq_weak_strong hΩ u hubound
  obtain ⟨σLim, _, ψ, hψ, hσweak⟩ := exists_weakly_convergent_subsequence
    (H := Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (fun n => σ (φ n)) (fun n => hσbound (φ n))
  have hscale := hε.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hvalue := hstrong.comp hψ.tendsto_atTop
  refine ⟨uLim, ?_, φ ∘ ψ, hφ.comp hψ,
    fun ℓ => (hweak ℓ).comp hψ.tendsto_atTop, hvalue⟩
  exact effective_equilibrium_of_weak_stress A hΩ f hscale hvalue
    (fun n => σ (φ (ψ n))) σLim hσweak
    (mul_nonneg (norm_nonneg A.field) (mul_nonneg hK.le (norm_nonneg f)))
    (Eventually.of_forall fun n => hσbound (φ (ψ n)))
    (Eventually.of_forall fun n => hσrep (φ (ψ n)))
    (Eventually.of_forall fun n => hσeq (φ (ψ n)))

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, uniqueness step: every approach sequence has a
subsequence converging to the fixed effective equilibrium. -/
private theorem static_subsequence_to_unique_equilibrium {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (f : SpatialL2 Ω)
    (u : ℝ → ZeroBoundaryH1 Ω)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field ε) (u ε) v = loadPairing f v)
    (u₀ : ZeroBoundaryH1 Ω)
    (huniq : ∀ w : ZeroBoundaryH1 Ω,
      (∀ v : ZeroBoundaryH1 Ω,
        (∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm A (symmetricGradient w x) (symmetricGradient v x)) =
            loadPairing f v) → w = u₀)
    (ns : ℕ → ℝ) (hns : Tendsto ns atTop (𝓝[>] (0 : ℝ))) :
    ∃ ms : ℕ → ℕ,
      (∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (ns (ms n)))) atTop (𝓝 (ℓ u₀))) ∧
      Tendsto (fun n => VectorH1.valueL Ω (u (ns (ms n))).val) atTop
        (𝓝 (VectorH1.valueL Ω u₀.val)) := by
  have hpos : ∀ᶠ n in atTop, 0 < ns n := hns.eventually self_mem_nhdsWithin
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  have htail (n : ℕ) : 0 < ns (n + N) := hN (n + N) (by omega)
  obtain ⟨uLim, hLim, φ, _, hweak, hstrong⟩ := static_equilibrium_subsequence A hΩ f
    (fun n => ns (n + N)) (hns.comp (tendsto_add_atTop_nat N)) htail
    (fun n => u (ns (n + N))) (fun n => hu _ (htail n))
  obtain rfl : uLim = u₀ := huniq uLim hLim
  exact ⟨fun n => φ n + N, hweak, hstrong⟩

/-- Theorem 3.1, static periodic homogenization in the Laplace-domain
argument: microscopic equilibria converge weakly in H¹₀ and strongly in
L² to the unique equilibrium of the actual effective cell form. -/
theorem periodic_elliptic_homogenization {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (f : SpatialL2 Ω) (u : ℝ → ZeroBoundaryH1 Ω)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field ε) (u ε) v = loadPairing f v) :
    ∃ u₀ : ZeroBoundaryH1 Ω,
      (∀ v : ZeroBoundaryH1 Ω,
        (∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm A (symmetricGradient u₀ x) (symmetricGradient v x)) =
            loadPairing f v) ∧
      (∀ w : ZeroBoundaryH1 Ω,
        (∀ v : ZeroBoundaryH1 Ω,
          (∫ x in (Ω : Set (PhysicalSpace d)),
            effectiveForm A (symmetricGradient w x) (symmetricGradient v x)) =
              loadPairing f v) → w = u₀) ∧
      (∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ u₀))) ∧
      Tendsto (fun ε => VectorH1.valueL Ω (u ε).val) (𝓝[>] (0 : ℝ))
        (𝓝 (VectorH1.valueL Ω u₀.val)) := by
  obtain ⟨u₀, heq, huniq⟩ := effective_elliptic_exists_unique A hΩ f
  refine ⟨u₀, heq, huniq, ?_, ?_⟩
  · intro ℓ
    exact tendsto_of_subseq_tendsto fun ns hns =>
      (static_subsequence_to_unique_equilibrium A hΩ f u hu u₀ huniq ns hns).imp
        fun _ h => h.1 ℓ
  · exact tendsto_of_subseq_tendsto fun ns hns =>
      (static_subsequence_to_unique_equilibrium A hΩ f u hu u₀ huniq ns hns).imp
        fun _ h => h.2

/-- Theorem 3.1, static limit identification: every weak H¹₀ limit
of equilibria along positive vanishing scales solves the effective equation. -/
theorem periodic_elliptic_weak_limit {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (f : SpatialL2 Ω) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (u : ℕ → ZeroBoundaryH1 Ω)
    (hu : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field (ε n)) (u n) v = loadPairing f v)
    (uLim : ZeroBoundaryH1 Ω)
    (hweak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ uLim))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient uLim x) (symmetricGradient v x)) =
          loadPairing f v := by
  obtain ⟨w, hw, φ, hφ, hwWeak, _⟩ :=
    static_equilibrium_subsequence A hΩ f ε hε hpos u hu
  have hwLim : w = uLim := by
    apply ext_inner_left ℝ
    intro z
    exact tendsto_nhds_unique (hwWeak (innerSL ℝ z))
      ((hweak (innerSL ℝ z)).comp hφ.tendsto_atTop)
  simpa only [hwLim] using hw

end KVApproximation.Homogenization
