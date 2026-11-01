module

public import KVApproximation.NeuralOperators.PronyResponses

/-!
# Isometric state coordinates for response mappings
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

variable {E Q Q' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup Q'] [NormedSpace ℝ Q']

/-- Lemma B.12: change only the internal-state coordinates in the full
stress input, preserving the Euclidean product norm. -/
def stressStateCoordinates (T : Q ≃ₗᵢ[ℝ] Q') :
    StressInput E Q ≃ₗᵢ[ℝ] StressInput E Q' :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E)
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E) T)

/-- Lemma B.12: change the internal-state coordinates in the full kinetic
input, retaining the strain velocity and the Euclidean product norm. -/
def kineticStateCoordinates (T : Q ≃ₗᵢ[ℝ] Q') :
    KineticInput E Q ≃ₗᵢ[ℝ] KineticInput E Q' :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E) T

/-- Lemma B.12 (`eq:ua_full_F_approx`): the Prony stress response written
in scalar state coordinates. -/
def coordinateStressResponse {n : ℕ} (P : PronyModel M E n)
    (T : BlockState n E ≃ₗᵢ[ℝ] Q) (a : M) (x : StressInput E Q) : E :=
  pronyStressResponse P a ((stressStateCoordinates T).symm x)

/-- Lemma B.12 (`eq:ua_full_G_approx`): the kinetic response with both its
state input and state derivative expressed in the same isometric coordinates. -/
def coordinateKineticResponse {n : ℕ} (P : PronyModel M E n)
    (T : BlockState n E ≃ₗᵢ[ℝ] Q) (a : M) (x : KineticInput E Q) : Q :=
  T (pronyKineticResponse P a ((kineticStateCoordinates T).symm x))

end KVApproximation.NeuralOperators
