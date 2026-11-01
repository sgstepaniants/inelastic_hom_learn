module

public import KVApproximation.Tensor.MandelBlocks
public import KVApproximation.Tensor.Dimensions
public import KVApproximation.Tensor.MandelIsometry

/-!
# Scalar indexing of concatenated Mandel vectors
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Lemma B.12: identify the independent strain components with a finite
scalar index set of the exact dimension. -/
def strainIndexEquivFin (d : ℕ) : StrainIndex d ≃ Fin (strainDimension d) :=
  Fintype.equivFinOfCardEq (card_strainIndex d)

/-- Example 2.1 and Lemma B.12: scalar indexing of the independent
fourth-order components, with the exact tensor dimension. -/
def elasticityIndexEquivFin (d : ℕ) : ElasticityIndex d ≃ Fin (elasticityDimension d) :=
  Fintype.equivFinOfCardEq (card_elasticityIndex d)

/-- Example 2.1 (`eq:F_and_G`): the prescribed strain Mandel vector
with consecutive scalar indices. -/
def scalarStrainMandel {d : ℕ} (e : Symmetric d) :
    EuclideanSpace ℝ (Fin (strainDimension d)) :=
  WithLp.toLp 2 (fun k => strainMandel e ((strainIndexEquivFin d).symm k))

/-- Example 2.1 (`eq:F_and_G`): the prescribed fourth-order Mandel
vector with consecutive scalar indices. -/
def scalarElasticityMandel {d : ℕ} (A : Elasticity d) :
    EuclideanSpace ℝ (Fin (elasticityDimension d)) :=
  WithLp.toLp 2 (fun k => elasticityMandel A ((elasticityIndexEquivFin d).symm k))

/-- Lemma B.12: flatten the block and Mandel component indices to the
paper's `n * d_𝒱²` scalar internal variables. -/
def blockMandelIndexEquiv (n d : ℕ) :
    Fin n × StrainIndex d ≃ Fin (n * strainDimension d) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (strainIndexEquivFin d)).trans finProdFinEquiv

/-- Lemmas B.11–B.12: the prescribed concatenated Mandel coordinates,
with a single finite scalar index. -/
def scalarBlockStrainMandel {n d : ℕ} (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    EuclideanSpace ℝ (Fin (n * strainDimension d)) :=
  WithLp.toLp 2 (fun k => blockStrainMandel q ((blockMandelIndexEquiv n d).symm k))

end KVApproximation.Tensor
