module

public import KVApproximation.Tensor.Spaces
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Mandel coordinates
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Example 2.1: the independent second-order tensor components. -/
abbrev StrainIndex (d : ℕ) := {p : Fin d × Fin d // p.1 ≤ p.2}

/-- Example 2.1: Frobenius weights of the diagonal and off-diagonal components. -/
def mandelWeight {d : ℕ} (p : StrainIndex d) : ℝ :=
  if p.val.1 = p.val.2 then 1 else Real.sqrt 2

/-- Example 2.1 (`eq:F_and_G`): second-order Mandel coordinates, indexed
by the upper triangular physical components. -/
def strainMandel {d : ℕ} (e : Symmetric d) : EuclideanSpace ℝ (StrainIndex d) :=
  WithLp.toLp 2 (fun p => mandelWeight p * e.val p.val)

/-- Example 2.1: ordering of strain coordinates for fourth-order vectorization. -/
def strainIndexCode {d : ℕ} (p : StrainIndex d) : ℕ := p.val.1.val * d + p.val.2.val

/-- Example 2.1: independent entries of the symmetric Mandel operator matrix. -/
abbrev ElasticityIndex (d : ℕ) :=
  {p : StrainIndex d × StrainIndex d // strainIndexCode p.1 ≤ strainIndexCode p.2}

/-- Example 2.1 (`eq:F_and_G`): fourth-order Mandel vectorization.
The two minor-symmetry weights form the operator matrix; the major-symmetry
weight vectorizes its upper triangle with the Frobenius norm. -/
def elasticityMandel {d : ℕ} (A : Elasticity d) : EuclideanSpace ℝ (ElasticityIndex d) :=
  WithLp.toLp 2 (fun p =>
    (if p.val.1 = p.val.2 then 1 else Real.sqrt 2) *
      mandelWeight p.val.1 * mandelWeight p.val.2 * A.val (p.val.1.val, p.val.2.val))

end KVApproximation.Tensor
