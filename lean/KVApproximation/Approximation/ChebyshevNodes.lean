module

public import KVApproximation.Approximation.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Tactic.Linarith

/-!
# Chebyshev root nodes and aliasing
-/

public section

namespace KVApproximation.Approximation

open Polynomial.Chebyshev

/-- Definition B.8: every root node lies in the reference interval. -/
theorem chebyshevNode_mem (m : ℕ) (i : Fin m) :
    chebyshevNode m i ∈ Set.Icc (-1 : ℝ) 1 :=
  Real.cos_mem_Icc _

/-- Definition B.8: the root nodes are pairwise distinct. -/
theorem chebyshevNode_injective (m : ℕ) :
    Function.Injective (chebyshevNode m) := by
  intro i j hij
  apply Fin.ext
  exact ((Finset.range m).nodup_map_iff_injOn.mp (roots_T_real_nodup m))
    (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) hij

/-- Definition B.8: the interpolation nodes are roots of `Tₘ`. -/
theorem chebyshevNode_isRoot (m : ℕ) (i : Fin m) :
    (T ℝ m).eval (chebyshevNode m i) = 0 := by
  apply Polynomial.isRoot_of_mem_roots
  rw [roots_T_real]
  change chebyshevNode m i ∈ (Finset.range m).image
    (fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (m : ℝ))))
  exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩

/-- Lemma B.9, proof: root-node interpolation is exact below degree `m`. -/
theorem chebyshev_interpolation_exact {m : ℕ} {p : Polynomial ℝ}
    (hp : p.degree < m) :
    Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => p.eval (chebyshevNode m i)) = p := by
  apply (Lagrange.eq_interpolate (chebyshevNode_injective m).injOn _).symm
  simpa using hp

/-- Lemma B.9, aliasing proof: reflection across the root degree changes sign. -/
private theorem root_reflection (m : ℕ) (i : Fin m) (k : ℤ) :
    (T ℝ ((m : ℤ) + k)).eval (chebyshevNode m i) =
      -(T ℝ ((m : ℤ) - k)).eval (chebyshevNode m i) := by
  have h := congrArg (Polynomial.eval (chebyshevNode m i)) (T_mul_T ℝ m k)
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add,
    chebyshevNode_isRoot, mul_zero, zero_mul] at h
  linarith

/-- Lemma B.9, proof: at the roots of `Tₘ`, every Chebyshev polynomial
agrees with zero or a signed Chebyshev polynomial of degree below `m`. -/
theorem chebyshev_root_alias {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : Polynomial ℝ,
      (∀ i : Fin m, p.eval (chebyshevNode m i) =
        (T ℝ k).eval (chebyshevNode m i)) ∧
      (p = 0 ∨ ∃ r : ℕ, r < m ∧ (p = T ℝ r ∨ p = -T ℝ r)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hkm : k < m
      · exact ⟨T ℝ k, fun _ => rfl, Or.inr ⟨k, hkm, Or.inl rfl⟩⟩
      by_cases hkm' : k = m
      · subst k
        exact ⟨0, fun i => by simp [chebyshevNode_isRoot], Or.inl rfl⟩
      have hmk : m < k := by omega
      by_cases h2 : k < 2 * m
      · refine ⟨-T ℝ (2 * m - k : ℕ), ?_, Or.inr ⟨2 * m - k, by omega, Or.inr rfl⟩⟩
        intro i
        have h := root_reflection m i ((k : ℤ) - m)
        rw [show (m : ℤ) + ((k : ℤ) - m) = k by omega,
          show (m : ℤ) - ((k : ℤ) - m) = (2 * m - k : ℕ) by omega] at h
        simpa only [Polynomial.eval_neg] using h.symm
      · obtain ⟨p, hp, hshape⟩ := ih (k - 2 * m) (by omega)
        refine ⟨-p, ?_, ?_⟩
        · intro i
          have h := root_reflection m i ((k : ℤ) - m)
          rw [show (m : ℤ) + ((k : ℤ) - m) = k by omega,
            show (m : ℤ) - ((k : ℤ) - m) = -((k - 2 * m : ℕ) : ℤ) by omega,
            T_neg] at h
          rw [Polynomial.eval_neg, hp, ← h]
        · rcases hshape with rfl | ⟨r, hr, hpr | hpr⟩
          · exact Or.inl neg_zero
          · exact Or.inr ⟨r, hr, Or.inr (congrArg Neg.neg hpr)⟩
          · exact Or.inr ⟨r, hr, Or.inl (by rw [hpr, neg_neg])⟩

/-- Lemma B.9, proof: interpolating a Chebyshev polynomial at the roots
of `Tₘ` has uniform norm at most one on the reference interval. -/
theorem chebyshev_interpolation_T_bound {m : ℕ} (hm : 0 < m) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => (T ℝ k).eval (chebyshevNode m i))).eval x| ≤ 1 := by
  obtain ⟨p, hp, hshape⟩ := chebyshev_root_alias hm k
  have hdegree : p.degree < m := by
    rcases hshape with rfl | ⟨r, hr, rfl | rfl⟩
    · simp
    · simpa [degree_T] using hr
    · simpa [degree_T] using hr
  have heq : Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => (T ℝ k).eval (chebyshevNode m i)) = p := by
    rw [← chebyshev_interpolation_exact hdegree]
    exact Lagrange.interpolate_eq_of_values_eq_on _ _ (fun i _ => (hp i).symm)
  rw [heq]
  rcases hshape with rfl | ⟨r, _, rfl | rfl⟩
  · simp
  · exact abs_eval_T_real_le_one _ (abs_le.mpr hx)
  · simpa only [Polynomial.eval_neg, abs_neg] using
      abs_eval_T_real_le_one (r : ℤ) (abs_le.mpr hx)

end KVApproximation.Approximation
