import LinearRouting.ExactPhaseTeleportation

/-!
# Coherent Pauli correction at Bob

The two work registers carry orthogonal spectral subspaces for the
two key bits. Bob can use those subspaces as controls for a unitary
Pauli correction without measuring the keys.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators Kronecker

noncomputable section

variable {W : Type*} [Fintype W]

private def bobCorrectionTerm
    (E₁ E₂ : Bool → Matrix W W ℂ) (key : Bool × Bool) :
    Matrix (Fin 2 × (W × W)) (Fin 2 × (W × W)) ℂ :=
  (pauli key)ᴴ ⊗ₖ (E₁ key.1 ⊗ₖ E₂ key.2)

/-- Correct the Pauli pad coherently on each joint work eigenspace. -/
def bobCorrection (E₁ E₂ : Bool → Matrix W W ℂ) :
    Matrix (Fin 2 × (W × W)) (Fin 2 × (W × W)) ℂ :=
  ∑ key : Bool × Bool, bobCorrectionTerm E₁ E₂ key

theorem bobCorrection_conjTranspose_mul [DecidableEq W]
    (E₁ E₂ : Bool → Matrix W W ℂ)
    (hHerm₁ : ∀ key, (E₁ key)ᴴ = E₁ key)
    (hHerm₂ : ∀ key, (E₂ key)ᴴ = E₂ key)
    (hMul₁ : ∀ key key', E₁ key * E₁ key' = if key = key' then E₁ key else 0)
    (hMul₂ : ∀ key key', E₂ key * E₂ key' = if key = key' then E₂ key else 0)
    (hSum₁ : ∑ key : Bool, E₁ key = 1)
    (hSum₂ : ∑ key : Bool, E₂ key = 1) :
    (bobCorrection E₁ E₂)ᴴ * bobCorrection E₁ E₂ = 1 := by
  have hterm (key key' : Bool × Bool) :
      (bobCorrectionTerm E₁ E₂ key)ᴴ * bobCorrectionTerm E₁ E₂ key' =
        if key = key' then (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
          (E₁ key.1 ⊗ₖ E₂ key.2) else 0 := by
    simp only [bobCorrectionTerm, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, hHerm₁, hHerm₂,
      ← Matrix.mul_kronecker_mul, hMul₁, hMul₂]
    rcases key with ⟨k₁, k₂⟩
    rcases key' with ⟨l₁, l₂⟩
    by_cases h₁ : k₁ = l₁ <;> by_cases h₂ : k₂ = l₂ <;>
      simp [h₁, h₂, pauli_mul_conjTranspose]
  unfold bobCorrection
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc
    (∑ key : Bool × Bool, (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (E₁ key.1 ⊗ₖ E₂ key.2)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        ((∑ key : Bool, E₁ key) ⊗ₖ (∑ key : Bool, E₂ key)) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool,
        Matrix.kronecker_add, Matrix.add_kronecker]
      abel
    _ = 1 := by rw [hSum₁, hSum₂, Matrix.one_kronecker_one, Matrix.one_kronecker_one]

/-- On the work subspace for the actual key, only that correction term acts. -/
theorem bobCorrection_mul_encoded
    (E₁ E₂ O₁ O₂ : Bool → Matrix W W ℂ)
    (hSupport₁ : ∀ key z, E₁ key * O₁ z = if key = z then O₁ z else 0)
    (hSupport₂ : ∀ key z, E₂ key * O₂ z = if key = z then O₂ z else 0)
    (key : Bool × Bool) :
    bobCorrection E₁ E₂ * (pauli key ⊗ₖ (O₁ key.1 ⊗ₖ O₂ key.2)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (O₁ key.1 ⊗ₖ O₂ key.2) := by
  have hterm (k : Bool × Bool) :
      bobCorrectionTerm E₁ E₂ k * (pauli key ⊗ₖ (O₁ key.1 ⊗ₖ O₂ key.2)) =
        if k = key then (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
          (O₁ key.1 ⊗ₖ O₂ key.2) else 0 := by
    simp only [bobCorrectionTerm, ← Matrix.mul_kronecker_mul, hSupport₁, hSupport₂]
    rcases k with ⟨k₁, k₂⟩
    rcases key with ⟨l₁, l₂⟩
    by_cases h₁ : k₁ = l₁ <;> by_cases h₂ : k₂ = l₂ <;>
      simp [h₁, h₂, pauli_conjTranspose_mul]
  unfold bobCorrection
  rw [Matrix.sum_mul]
  simp_rw [hterm]
  simp

/-- The corrected amplitude has the original qubit basis value and the
original two work amplitudes. -/
theorem bobCorrection_decode_amplitude
    (E₁ E₂ O₁ O₂ : Bool → Matrix W W ℂ)
    (hSupport₁ : ∀ key z, E₁ key * O₁ z = if key = z then O₁ z else 0)
    (hSupport₂ : ∀ key z, E₂ key * O₂ z = if key = z then O₂ z else 0)
    (key : Bool × Bool) (out input : Fin 2) (p₁ p'₁ p₂ p'₂ : W) :
    (∑ c : Fin 2 × (W × W),
      bobCorrection E₁ E₂ (out, p₁, p₂) c *
        (pauli key c.1 input * O₁ key.1 c.2.1 p'₁ * O₂ key.2 c.2.2 p'₂)) =
      if out = input then O₁ key.1 p₁ p'₁ * O₂ key.2 p₂ p'₂ else 0 := by
  have h := congrArg (fun M : Matrix (Fin 2 × (W × W)) (Fin 2 × (W × W)) ℂ ↦
    M (out, p₁, p₂) (input, p'₁, p'₂))
    (bobCorrection_mul_encoded E₁ E₂ O₁ O₂ hSupport₁ hSupport₂ key)
  by_cases hEq : out = input
  · simpa [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply, hEq, mul_assoc] using h
  · simpa [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply, hEq, mul_assoc] using h

end

end LinearRouting.ExactPhase
