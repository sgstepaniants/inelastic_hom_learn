module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Finite Euclidean coordinates in L²
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, spatial Sobolev foundations: assembling finitely many L²
fields preserves the Euclidean sum of their squared norms. This is valid
for arbitrary measures and includes an empty coordinate type. -/
theorem lp_finite_coordinates {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (μ : Measure X) :
    ∃ U : PiLp 2 (fun i => Lp (E i) 2 μ) ≃ₗᵢ[ℝ] Lp (PiLp 2 E) 2 μ,
      ∀ f : PiLp 2 (fun i => Lp (E i) 2 μ),
        ∀ᵐ x ∂μ, U f x = WithLp.toLp 2 (fun i => f i x) := by
  classical
  have hmem (f : PiLp 2 (fun i => Lp (E i) 2 μ)) :
      MemLp (fun x => WithLp.toLp 2 (fun i => f i x)) 2 μ :=
    MemLp.of_eval_piLp fun i => Lp.memLp (f i)
  let A₀ (f : PiLp 2 (fun i => Lp (E i) 2 μ)) : Lp (PiLp 2 E) 2 μ :=
    (hmem f).toLp (fun x => WithLp.toLp 2 (fun i => f i x))
  have hA (f : PiLp 2 (fun i => Lp (E i) 2 μ)) :
      ∀ᵐ x ∂μ, A₀ f x = WithLp.toLp 2 (fun i => f i x) :=
    (hmem f).coeFn_toLp
  let A : PiLp 2 (fun i => Lp (E i) 2 μ) →ₗ[ℝ] Lp (PiLp 2 E) 2 μ :=
    { toFun := A₀
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [hA (f + g), hA f, hA g, Lp.coeFn_add (A₀ f) (A₀ g),
          ae_all_iff.mpr (fun i => Lp.coeFn_add (f i) (g i))] with x hfg hf hg hadd hi
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        apply PiLp.ext
        intro i
        exact hi i
      map_smul' := by
        intro r f
        apply Lp.ext
        filter_upwards [hA (r • f), hA f, Lp.coeFn_smul r (A₀ f),
          ae_all_iff.mpr (fun i => Lp.coeFn_smul r (f i))] with x hrf hf hsmul hi
        change A₀ (r • f) x = (r • A₀ f) x
        rw [hrf, hsmul, Pi.smul_apply, hf]
        apply PiLp.ext
        intro i
        exact hi i }
  have hnorm (f : PiLp 2 (fun i => Lp (E i) 2 μ)) : ‖A f‖ = ‖f‖ := by
    have hs : ‖A f‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
      rw [← Lp.integral_norm_sq_eq_norm_sq]
      calc
        (∫ x, ‖A f x‖ ^ 2 ∂μ) = ∫ x, ∑ i, ‖f i x‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [hA f] with x hx
          change ‖A₀ f x‖ ^ 2 = _
          rw [hx, PiLp.norm_sq_eq_of_L2]
        _ = ∑ i, ∫ x, ‖f i x‖ ^ 2 ∂μ := by
          exact integral_finsetSum Finset.univ fun i _ => (Lp.memLp (f i)).norm.integrable_sq
        _ = ∑ i, ‖f i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Lp.integral_norm_sq_eq_norm_sq (f i)
    rw [← PiLp.norm_sq_eq_of_L2] at hs
    nlinarith [norm_nonneg (A f), norm_nonneg f]
  let J : PiLp 2 (fun i => Lp (E i) 2 μ) →ₗᵢ[ℝ] Lp (PiLp 2 E) 2 μ :=
    { A with norm_map' := hnorm }
  have hsurj : Function.Surjective J := by
    intro f
    let g : PiLp 2 (fun i => Lp (E i) 2 μ) :=
      WithLp.toLp 2 (fun i => (PiLp.proj (𝕜 := ℝ) 2 E i).compLp f)
    refine ⟨g, ?_⟩
    apply Lp.ext
    filter_upwards [hA g,
      ae_all_iff.mpr (fun i => (PiLp.proj (𝕜 := ℝ) 2 E i).coeFn_compLp f)] with x hx hi
    change A₀ g x = f x
    rw [hx]
    apply PiLp.ext
    intro i
    exact hi i
  exact ⟨LinearIsometryEquiv.ofSurjective J hsurj, hA⟩

end KVApproximation.Analysis
