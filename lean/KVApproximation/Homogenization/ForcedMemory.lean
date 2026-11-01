module

public import KVApproximation.Homogenization.HomogenizedMemory
public import KVApproximation.Analysis.TimeSobolevGreen

/-!
# The forced homogenized memory equation

The spatial Green balance and an actual Sobolev realization of its Duhamel
convolution recover the forced weak equation.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, forcing assembly: normalize a bilinear memory kernel
before specializing the Sobolev Green identity to spatial duals. -/
private theorem memory_equation_of_bilinear_green_trace
    {F H Y Z : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (L : Z →L[ℝ] H →L[ℝ] Y) (V E : Z) (K : ℝ → Z) (hK : Continuous K)
    (G : ℝ → F →L[ℝ] H) (hG : Continuous G) (B : F →L[ℝ] Y)
    (hbalance : ∀ (g : F) (t : ℝ), 0 ≤ t →
      L V (G t g) + L E (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution K (fun r => G r g) L volume t = B g)
    (f : ℝ → F) (hf : IntervalIntegrable f volume 0 T)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT u t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) :
    TimeH1.initial hT u = 0 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        L V (TimeH1.velocity u t) + L E (TimeH1.value u t) +
          posConvolution K (TimeH1.velocity u) L volume t = B (f t) := by
  have hb (t : ℝ) (ht : 0 ≤ t) (g : F) :
      L V (G t g) + L E (∫ r in (0 : ℝ)..t, G r g) +
        (∫ r in (0 : ℝ)..t, L (K (t - r)) (G r g)) = B g := by
    have h := hbalance g t ht
    rw [posConvolution_eq_integral_sub L K _ ht] at h
    exact h
  simpa only [posConvolution, ContinuousLinearMap.id_apply] using
    TimeH1.memory_equation_of_green_trace hT u (L V) (L E) (fun t => L (K t)) G B
      (L.continuous.comp hK) hG hb f hf htrace

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ForcedMemory.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ForcedMemory.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel forcing:
an actual H¹ realization of the spatial Green convolution satisfies the
homogenized weak equation with L² forcing and zero initial displacement. -/
theorem green_trace_isHomogenizedSolution {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hbalance : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      constantSpatialFormL (Ω := Ω) Vhom (G t g) +
        constantSpatialFormL (Ω := Ω) Ehom (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution K (fun r => G r g) (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g)
    (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT u t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) :
    TimeH1.initial hT u = 0 ∧ IsHomogenizedSolution hT Vhom Ehom K 0 f u := by
  have hf : IntervalIntegrable (fun t => f t) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((Lp.memLp f).integrable (by norm_num))
  have h := memory_equation_of_bilinear_green_trace hT u
    (constantSpatialFormL (Ω := Ω)) Vhom Ehom K hK G hG
    (spatialLoadOperator (Ω := Ω)) hbalance (fun t => f t) hf htrace
  refine ⟨h.1, (isHomogenizedSolution_iff_memory_equation hT Vhom Ehom K hK 0 f u).mpr
    ⟨?_, h.2⟩⟩
  exact (congrArg (constantSpatialFormL (Ω := Ω) Ehom) h.1).trans
    ((constantSpatialFormL (Ω := Ω) Ehom).map_zero.trans
      (spatialLoadOperator (Ω := Ω)).map_zero.symm)

end KVApproximation.Homogenization
