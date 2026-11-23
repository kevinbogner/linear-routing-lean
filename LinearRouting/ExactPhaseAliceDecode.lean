import LinearRouting.ExactPhaseTeleportation

/-!
# Alice's decoder in a fixed flag branch

Alice uses her coherent key to restore the two work pairs, then inverts the
Bell transform. The resulting amplitude factors into the recovered input and
three pairs of equal basis indices on the discarded registers.
-/

namespace LinearRouting.ExactPhase

open Matrix

variable {W : Type*}

/-- The work corrections controlled by the retained key, followed by the
inverse Bell transform. -/
noncomputable def aliceDecode (O₁ O₂ : Bool → Matrix W W ℂ) :
    Matrix ((Fin 2 × Fin 2) × (W × W)) ((Bool × Bool) × (W × W)) ℂ :=
  Matrix.of fun out input ↦
    bellᴴ out.1 input.1 * O₁ input.1.1 out.2.1 input.2.1 *
      O₂ input.1.2 out.2.2 input.2.2

@[simp] theorem aliceDecode_apply (O₁ O₂ : Bool → Matrix W W ℂ)
    (out : (Fin 2 × Fin 2) × (W × W)) (input : (Bool × Bool) × (W × W)) :
    aliceDecode O₁ O₂ out input =
      bellᴴ out.1 input.1 * O₁ input.1.1 out.2.1 input.2.1 *
        O₂ input.1.2 out.2.2 input.2.2 := rfl

variable [Fintype W]

private theorem sum_product_two (a : ℂ) (f g : W → ℂ) :
    a * (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, a * f i * g j := by
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.mul_sum, mul_assoc]

variable [DecidableEq W]

theorem aliceDecode_isometry (O₁ O₂ : Bool → Matrix W W ℂ)
    (h₁ : ∀ z, (O₁ z)ᴴ * O₁ z = 1) (h₂ : ∀ z, (O₂ z)ᴴ * O₂ z = 1) :
    (aliceDecode O₁ O₂)ᴴ * aliceDecode O₁ O₂ = 1 := by
  ext ⟨k, p₁, p₂⟩ ⟨l, q₁, q₂⟩
  calc
    _ = ∑ qt : Fin 2 × Fin 2,
          (star (bellᴴ qt k) * bellᴴ qt l) *
            ((O₁ k.1)ᴴ * O₁ l.1) p₁ q₁ * ((O₂ k.2)ᴴ * O₂ l.2) p₂ q₂ := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun qt _ ↦ ?_
      rw [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.mul_apply, sum_product_two]
      simp only [Matrix.conjTranspose_apply, aliceDecode_apply, star_mul]
      refine Finset.sum_congr rfl fun newP₁ _ ↦ ?_
      refine Finset.sum_congr rfl fun newP₂ _ ↦ ?_
      ring
    _ = ((bellᴴ)ᴴ * bellᴴ) k l *
          ((O₁ k.1)ᴴ * O₁ l.1) p₁ q₁ * ((O₂ k.2)ᴴ * O₂ l.2) p₂ q₂ := by
      rw [Matrix.mul_apply (M := (bellᴴ)ᴴ), Finset.sum_mul, Finset.sum_mul]
      rfl
    _ = _ := by
      rw [Matrix.conjTranspose_conjTranspose, bell_mul_conjTranspose]
      by_cases hk : k = l
      · subst l
        rw [h₁, h₂]
        by_cases hp₁ : p₁ = q₁ <;> by_cases hp₂ : p₂ = q₂ <;>
          simp [Matrix.one_apply, hp₁, hp₂]
      · simp [hk]

/-- Applying Alice's decoder in a zero cell gives the input qubit at Alice,
with the Bell and work pairs independent of the input. -/
theorem aliceDecode_amplitude (O₁ O₂ : Bool → Matrix W W ℂ)
    (h₁ : ∀ z, O₁ z * (O₁ z)ᵀ = 1) (h₂ : ∀ z, O₂ z * (O₂ z)ᵀ = 1)
    (q c out anc : Fin 2) (p₁ p₂ newP₁ newP₂ : W) :
    (∑ old : (Bool × Bool) × (W × W),
      aliceDecode O₁ O₂ ((out, anc), newP₁, newP₂) old *
        ((2 : ℂ)⁻¹ * pauli old.1 c q *
          O₁ old.1.1 p₁ old.2.1 * O₂ old.1.2 p₂ old.2.2)) =
      if out = q then
        if anc = c ∧ newP₁ = p₁ ∧ newP₂ = p₂ then invSqrtTwo else 0
      else 0 := by
  calc
    _ = ∑ k : Bool × Bool,
          (star (bell k (out, anc)) * ((2 : ℂ)⁻¹ * pauli k c q)) *
            (O₁ k.1 * (O₁ k.1)ᵀ) newP₁ p₁ *
            (O₂ k.2 * (O₂ k.2)ᵀ) newP₂ p₂ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.mul_apply, sum_product_two]
      simp only [aliceDecode_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun oldP₁ _ ↦ ?_
      refine Finset.sum_congr rfl fun oldP₂ _ ↦ ?_
      ring
    _ = _ := by
      by_cases hP₁ : newP₁ = p₁
      · by_cases hP₂ : newP₂ = p₂
        · simp only [h₁, h₂, hP₁, hP₂, Matrix.one_apply_eq, mul_one, and_true]
          rw [bell_decode_amplitude]
          rfl
        · simp [h₁, h₂, hP₁, hP₂]
      · simp [h₁, h₂, Matrix.one_apply, hP₁]

end LinearRouting.ExactPhase
