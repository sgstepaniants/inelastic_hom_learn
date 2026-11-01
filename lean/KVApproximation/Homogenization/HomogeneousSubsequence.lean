module

public import KVApproximation.Homogenization.MicroscopicCompactness
public import KVApproximation.Homogenization.HomogeneousLimit

/-!
# Homogenized limits of prepared microscopic subsequences
-/

public section

noncomputable section

open TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, initial traces: weak time-Sobolev convergence preserves
initial data through the continuous trace operator. -/
private theorem weak_initial_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (u : ℕ → TimeH1 H T) (uLim : TimeH1 H T)
    (hu : ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ uLim)))
    (q : ℕ → H) (hq : ∀ n, TimeH1.initial hT (u n) = q n) :
    ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ (TimeH1.initial hT uLim))) := by
  intro ℓ
  have h := TimeH1.weak_trace_tendsto hT u uLim hu ⟨0, le_rfl, hT.le⟩ ℓ
  change Tendsto (fun n => ℓ (TimeH1.initial hT (u n))) atTop
    (𝓝 (ℓ (TimeH1.initial hT uLim))) at h
  exact h.congr' (Eventually.of_forall fun n => congrArg ℓ (hq n))

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, zero-forcing compactness: every positive approach sequence
has a weak time-Sobolev subsequence solving the actual cell-memory equation.
The initial weak limit is obtained by evaluating the weak trace at zero. -/
theorem prepared_homogeneous_subsequence
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (Ω := Ω) (rescalePeriodic E.field (ε n)) (q n) w = loadPairing (Ω := Ω) g₀ w)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ n, IsMicroscopicSolution (Ω := Ω) (T := T) hT V E (ε n) (q n) 0 (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution (Ω := Ω) (T := T) hT C.viscosity C.elasticity C.kernel g₀ 0 uLim ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  have hb := periodic_elliptic_uniform_bound (Ω := Ω) E hΩ
  have hB := hb.choose_spec.2
  have hc := microscopic_homogeneous_subsequence (Ω := Ω) (T := T)
    (B := hb.choose * ‖g₀‖) V E hΩ hT ε hpos q
    (fun n => hB (ε n) (hpos n) g₀ (q n) (hq n)) u hu
  obtain ⟨φ, hφ, uLim, v, hv, ⟨M, hM, hbound, hLip⟩, htrace, hweak, hpoint, hLap⟩ := hc
  have hinit := weak_initial_tendsto (H := ZeroBoundaryH1 Ω) (T := T) hT
    (fun n => u (φ n)) uLim hweak (fun n => q (φ n))
    (fun n => (hu (φ n)).1)
  refine ⟨φ, hφ, uLim, ?_, hweak⟩
  exact @homogeneous_limit_isHomogenizedSolution d Ω V E C hΩ T hT
    (fun n => ε (φ n)) (hε.comp hφ.tendsto_atTop) (fun n => hpos (φ n))
    (fun n => q (φ n)) g₀ (fun n => hq (φ n)) uLim v hv M
    hbound htrace hinit hLap


end KVApproximation.Homogenization
