module

public import KVApproximation.OperatorTheory.SpectralBounds
public import Mathlib.Tactic.Linarith

/-!
# The resolvent identity for effective forms

The transformed cell problem identifies the resolvent compression with the
difference between the combined effective form and the separate effective forms.
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.1: the variational identity also holds in the second entry. -/
private theorem form_projection_right (A : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (u : X) (v : H) : A.form u (A.projection X v) = A.form u v := by
  rw [A.symmetric, form_projection, A.symmetric]

/-- Theorem 3.1, transformed cell problem: the two projection differences
are related by the relaxation operator. -/
private theorem relaxation_projection_difference (V E A : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (s : ℝ) (hs : 0 < s)
    (hA : ∀ u v, A.form u v = V.form u v + s⁻¹ * E.form u v) (u : H) :
    relaxation V E X (A.projection X u - E.projection X u) =
      s • (V.projection X u - A.projection X u) := by
  apply (V.restrict X).eq_of_form_eq
  intro z
  change V.form (relaxation V E X _) z = V.form _ z
  rw [relaxation_spec]
  change E.form ((A.projection X u : H) - E.projection X u) z =
    V.form (s • ((V.projection X u : H) - A.projection X u)) z
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, form_projection]
  have hp := form_projection A X u z
  rw [hA, hA] at hp
  have hm := congrArg (s * ·) hp
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hm
  linarith

/-- Theorem 3.1, transformed cell problem: positivity of the combined
form determines the solution of the shifted relaxation equation. -/
private theorem shifted_relaxation_injective (V E A : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (s : ℝ) (hs : 0 < s)
    (hA : ∀ u v, A.form u v = V.form u v + s⁻¹ * E.form u v) :
    Function.Injective (fun z : X => s • z + relaxation V E X z) := by
  have ht (z v : X) :
      A.form z v = s⁻¹ * V.form (s • z + relaxation V E X z : X) v := by
    change A.form z v = s⁻¹ * V.form (s • (z : H) + relaxation V E X z) v
    rw [hA]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      relaxation_spec, mul_add, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  intro x y hxy
  dsimp only at hxy
  apply (A.restrict X).eq_of_form_eq
  intro v
  change A.form x v = A.form y v
  rw [ht, ht, hxy]

/-- Theorem 3.1 and Lemma B.6: expansion of the effective forms after
the tested cell equations have removed the correctors. -/
private theorem effective_form_difference (V E A : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (s : ℝ)
    (hA : ∀ u v, A.form u v = V.form u v + s⁻¹ * E.form u v) (u v : H) :
    A.form u (A.complement X v) - V.form u (V.complement X v) -
        s⁻¹ * E.form u (E.complement X v) =
      V.form ((V.projection X u : H) - A.projection X u)
        ((V.projection X v : H) - E.projection X v) := by
  have hp := form_projection A X u (E.projection X v)
  rw [hA, hA, form_projection_right E X, ← form_projection V X u,
    ← form_projection E X u, form_projection_right E X] at hp
  rw [← complement_selfAdjoint, ← complement_selfAdjoint V,
    ← complement_selfAdjoint E, complement_apply, complement_apply, complement_apply, hA]
  simp only [map_sub, sub_apply]
  rw [form_projection_right V X, form_projection_right V X]
  linarith

/-- Theorem 3.1, transformed cell identity, and Lemma B.6: the resolvent
compression is the difference between the combined effective form and the
two separate effective forms. -/
theorem homogenizedForm_resolvent
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (s : ℝ) (hs : 0 < s)
    (hA : ∀ u v, A.form u v = V.form u v + s⁻¹ * E.form u v)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) (e g : F) :
    ⟪cfc (fun r => r / (s + r)) (weightedRelaxation V E X)
        (weightedMismatch V E X ι e), weightedMismatch V E X ι g⟫_ℝ =
      A.homogenizedForm X ι e g - V.homogenizedForm X ι e g -
        s⁻¹ * E.homogenizedForm X ι e g := by
  let R := weightedRelaxation V E X
  let w : ℝ → ℝ := fun r => r / (s + r)
  have hR : IsSelfAdjoint R := weightedRelaxation_isSelfAdjoint V E X
  have hspec : spectrum ℝ R ⊆ Set.Icc (αE / βV) (βE / αV) := by
    rw [weightedRelaxation_spectrum_eq]
    exact relaxation_spectrum_subset V E X hαV hβV hαE hβE hV hE
  have hsr (r : ℝ) (hr : r ∈ spectrum ℝ R) : 0 < s + r :=
    add_pos hs (lt_of_lt_of_le (div_pos hαE hβV) (hspec hr).1)
  have hw : ContinuousOn w (spectrum ℝ R) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (hsr r hr).ne')
  have hshift : cfc (fun r : ℝ => s + r) R = algebraMap ℝ _ s + R := by
    rw [cfc_const_add s (fun r : ℝ => r) R continuousOn_id hR, cfc_id' ℝ R hR]
  have hproduct : (algebraMap ℝ _ s + R) * cfc w R = R := by
    rw [← hshift, ← cfc_mul (fun r : ℝ => s + r) w R
      (continuousOn_const.add continuousOn_id) hw]
    calc
      _ = cfc (fun r : ℝ => r) R := cfc_congr fun r hr => by
        change (s + r) * (r / (s + r)) = r
        exact mul_div_cancel₀ r (hsr r hr).ne'
      _ = R := cfc_id' ℝ R hR
  let b : X := V.projection X (ι e) - A.projection X (ι e)
  have hb : s • b + relaxation V E X b = relaxation V E X (mismatch V E X (ι e)) := by
    have hrel := relaxation_projection_difference V E A X s hs hA (ι e)
    have hsplit : mismatch V E X (ι e) =
        (A.projection X (ι e) - E.projection X (ι e)) + b := by
      change V.projection X (ι e) - E.projection X (ι e) =
        (A.projection X (ι e) - E.projection X (ι e)) +
          (V.projection X (ι e) - A.projection X (ι e))
      abel
    rw [hsplit, map_add, hrel]
  have hcalc : (cfc w R (weightedMismatch V E X ι e)).val = b := by
    apply shifted_relaxation_injective V E A X s hs hA
    dsimp only
    rw [hb]
    have hh := congrArg (fun T : RelaxationSpace V X →L[ℝ] RelaxationSpace V X =>
      (T (weightedMismatch V E X ι e)).val) hproduct
    exact hh
  change V.form ((cfc w R (weightedMismatch V E X ι e)).val : H)
    (mismatch V E X (ι g)) = _
  rw [hcalc]
  exact (effective_form_difference V E A X s hA (ι e) (ι g)).symm

end KVApproximation.OperatorTheory
