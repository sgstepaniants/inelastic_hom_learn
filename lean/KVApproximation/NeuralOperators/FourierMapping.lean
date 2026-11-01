module

public import KVApproximation.Analysis.PeriodicCell
public import KVApproximation.NeuralOperators.Classes
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Fourier neural mappings with linear lifting and projection
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: a Euclidean channel vector. -/
abbrev Channels (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Example 2.1: the periodic L² function input, in channel coordinates. -/
abbrev ChannelField (d n : ℕ) := Lp (Channels n) 2 (cellMeasure d)

/-- Example 2.1: the rectangular set of retained Fourier modes. -/
def frequencyBox {d : ℕ} (cutoff : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j => Finset.Icc (-(cutoff j : ℤ)) (cutoff j : ℤ))

/-- Example 2.1: Fourier coefficients of real channel fields on the normalized cell. -/
def channelFourier {d n : ℕ} (h : PeriodicCell d → Channels n)
    (k : Fin d → ℤ) (j : Fin n) : ℂ :=
  ∫ y, UnitAddTorus.mFourier (-k) y * (h y j : ℂ) ∂cellMeasure d

/-- Example 2.1: one Fourier layer, with a pointwise real matrix and
conjugate-symmetric Fourier matrices. -/
structure FourierLayer (d input output : ℕ) where
  localWeight : Matrix (Fin output) (Fin input) ℝ
  bias : Fin output → ℝ
  cutoff : Fin d → ℕ
  multiplier : (Fin d → ℤ) →₀ Matrix (Fin output) (Fin input) ℂ
  support_subset : multiplier.support ⊆ frequencyBox cutoff
  conjugate_symmetry : ∀ k i j, multiplier (-k) i j = star (multiplier k i j)

/-- Example 2.1: Fourier part of a layer before taking its real value.
Conjugate symmetry implies that its imaginary part is zero. -/
def FourierLayer.fourierPart {d input output : ℕ} (L : FourierLayer d input output)
    (h : PeriodicCell d → Channels input) (y : PeriodicCell d) (i : Fin output) : ℂ :=
  ∑ k ∈ frequencyBox L.cutoff,
    (∑ j : Fin input, L.multiplier k i j * channelFourier h k j) * UnitAddTorus.mFourier k y

/-- Example 2.1: coordinatewise activation of the affine Fourier layer. -/
def FourierLayer.eval {d input output : ℕ} (L : FourierLayer d input output)
    (σ : ℝ → ℝ) (h : PeriodicCell d → Channels input) (y : PeriodicCell d) : Channels output :=
  WithLp.toLp 2 (fun i => σ
    ((∑ j : Fin input, L.localWeight i j * h y j) + (L.fourierPart h y i).re + L.bias i))

/-- Example 2.1: a finite chain with arbitrary intermediate widths. -/
inductive FourierChain (d : ℕ) : ℕ → ℕ → Type where
  | nil (width : ℕ) : FourierChain d width width
  | cons {input middle output : ℕ} (layer : FourierLayer d input middle)
      (rest : FourierChain d middle output) : FourierChain d input output

/-- Example 2.1: composition of the prescribed Fourier layers. -/
def FourierChain.eval {d input output : ℕ} (σ : ℝ → ℝ) :
    FourierChain d input output → (PeriodicCell d → Channels input) →
      PeriodicCell d → Channels output
  | .nil _, h => h
  | .cons L rest, h => rest.eval σ (L.eval σ h)

/-- Example 2.1: the Fourier-space projection to a finite channel vector. -/
structure FourierProjection (d input output : ℕ) where
  cutoff : Fin d → ℕ
  multiplier : (Fin d → ℤ) →₀ Matrix (Fin output) (Fin input) ℂ
  support_subset : multiplier.support ⊆ frequencyBox cutoff
  conjugate_symmetry : ∀ k i j, multiplier (-k) i j = star (multiplier k i j)

/-- Example 2.1: the complex sum in the Fourier projection. -/
def FourierProjection.complexValue {d input output : ℕ}
    (P : FourierProjection d input output) (h : PeriodicCell d → Channels input)
    (i : Fin output) : ℂ :=
  ∑ k ∈ frequencyBox P.cutoff, ∑ j : Fin input,
    P.multiplier k i j * channelFourier h k j

/-- Example 2.1: evaluation of the conjugate-symmetric Fourier projection. -/
def FourierProjection.eval {d input output : ℕ} (P : FourierProjection d input output)
    (h : PeriodicCell d → Channels input) : Channels output :=
  WithLp.toLp 2 (fun i => (P.complexValue h i).re)

/-- Remark 4.3 (`rmk:fnm_admissible`): the concrete architecture with linear
lifting and output maps, as used in its universal-approximation assertion. -/
structure FourierMapping (d vectorInput functionInput output : ℕ) where
  liftWidth : ℕ
  hiddenWidth : ℕ
  projectionWidth : ℕ
  lifting : WithLp 2 (Channels vectorInput × Channels functionInput) →ₗ[ℝ] Channels liftWidth
  layers : FourierChain d liftWidth hiddenWidth
  projection : FourierProjection d hiddenWidth projectionWidth
  outputMap : Channels projectionWidth →ₗ[ℝ] Channels output

/-- Example 2.1: evaluation on a representative of the function input. -/
def FourierMapping.evalRepresentative {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) (σ : ℝ → ℝ)
    (v : Channels vectorInput) (h : PeriodicCell d → Channels functionInput) : Channels output :=
  P.outputMap (P.projection.eval (P.layers.eval σ
    (fun y => P.lifting (WithLp.toLp 2 (v, h y)))))

/-- Example 2.1: evaluation of the entire Fourier neural mapping on L² inputs. -/
def FourierMapping.eval {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) (σ : ℝ → ℝ)
    (x : Channels vectorInput × ChannelField d functionInput) : Channels output :=
  P.evalRepresentative σ x.1 x.2

/-- Remark 4.3: continuous maps realized by the stated concrete architecture.
The defining representation contains actual finite network data. -/
def fourierMappingClass (σ : ℝ → ℝ) (d vectorInput functionInput output : ℕ) :
    Set C(Channels vectorInput × ChannelField d functionInput, Channels output) :=
  {Φ | ∃ P : FourierMapping d vectorInput functionInput output, ∀ x, Φ x = P.eval σ x}

end KVApproximation.NeuralOperators
