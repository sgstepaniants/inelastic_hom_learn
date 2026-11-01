module

public import KVApproximation.Homogenization.CellTensorBounds
public import KVApproximation.Homogenization.SpatialCoercivity
public import KVApproximation.Tensor.FormRepresentation

/-!
# Equilibrium for the effective cell form

The symmetric cell form has a constant elasticity-tensor representative.
Its inherited lower bound and the Dirichlet Korn estimate give the
effective equilibrium by the spatial Lax–Milgram theorem.
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static effective problem (`eq:homogenized_tensors`):
the actual cell form gives a unique Dirichlet equilibrium for every L² load. -/
theorem effective_elliptic_exists_unique {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (f : SpatialL2 Ω) :
    ∃! u : ZeroBoundaryH1 Ω, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient u x) (symmetricGradient v x)) =
          loadPairing f v := by
  have hsym (e g : Symmetric d) : effectiveForm A e g = effectiveForm A g e := by
    change A.toForm.form (constantStrainL d e)
        (A.toForm.complement (correctorSubspace d) (constantStrainL d g)) =
      A.toForm.form (constantStrainL d g)
        (A.toForm.complement (correctorSubspace d) (constantStrainL d e))
    rw [form_complement A.toForm (correctorSubspace d) (constantStrainL d e),
      form_complement A.toForm (correctorSubspace d) (constantStrainL d g)]
    exact A.toForm.symmetric _ _
  obtain ⟨H, hH, _⟩ := existsUnique_form_tensor (effectiveForm A) hsym
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  have hm : MemLp (fun _ : PhysicalSpace d => H) ⊤ μ := memLp_top_const H
  let AH := hm.toLp (fun _ : PhysicalSpace d => H)
  have hAH : AH =ᵐ[μ] fun _ => H := hm.coeFn_toLp
  have hbound : ∀ᵐ x ∂μ, ∀ e : Symmetric d,
      A.lower * ‖e‖ ^ 2 ≤ ⟪e, action (AH x) e⟫_ℝ := by
    filter_upwards [hAH] with x hx
    intro e
    rw [hx, hH]
    exact (effectiveForm_bounds A A.lower_pos A.bounds e).1
  have heq (u v : ZeroBoundaryH1 Ω) : spatialForm AH u v =
      ∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient u x) (symmetricGradient v x) := by
    apply integral_congr_ae
    filter_upwards [hAH] with x hx
    rw [hx, hH]
  simpa only [heq] using elliptic_exists_unique AH hΩ A.lower_pos hbound f

end KVApproximation.Homogenization
