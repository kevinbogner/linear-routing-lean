import Mathlib

/-!
# The Bell transform for coherent teleportation

The Bell transform replaces the Bell measurement by a change of basis. Its
outcome register is retained coherently, so the transform can also be undone.
-/

namespace LinearRouting.ExactPhase

open Matrix

/-- The amplitude of each term in a normalized Bell pair. -/
noncomputable def invSqrtTwo : ℂ := (↑(Real.sqrt 2) : ℂ)⁻¹

@[simp] theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

@[simp] theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  have h : (↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2) = 2 := by
    exact_mod_cast (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [invSqrtTwo, ← mul_inv, h]

/-- Computational-basis matrix of the Pauli pad `X^a Z^b` for `key = (a,b)`. -/
def pauli (key : Bool × Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun out input ↦
    if out = (if key.1 then 1 - input else input) then
      if key.2 && input == 1 then -1 else 1
    else 0

@[simp] theorem star_pauli_apply (key : Bool × Bool) (out input : Fin 2) :
    star (pauli key out input) = pauli key out input := by
  unfold pauli
  simp only [Matrix.of_apply]
  split_ifs <;> simp

theorem pauli_mul_conjTranspose (key : Bool × Bool) :
    pauli key * (pauli key)ᴴ = 1 := by
  rcases key with ⟨a, b⟩
  ext i j
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, pauli]

theorem pauli_conjTranspose_mul (key : Bool × Bool) :
    (pauli key)ᴴ * pauli key = 1 := by
  rcases key with ⟨a, b⟩
  ext i j
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, pauli]

/-- The Bell transform from the input and local Bell-pair half to the coherent key. -/
noncomputable def bell : Matrix (Bool × Bool) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun key (q, t) ↦ invSqrtTwo * pauli key t q

@[simp] theorem bell_apply (key : Bool × Bool) (q t : Fin 2) :
    bell key (q, t) = invSqrtTwo * pauli key t q := rfl

@[simp] theorem star_bell_apply (key : Bool × Bool) (qt : Fin 2 × Fin 2) :
    star (bell key qt) = bell key qt := by
  rcases qt with ⟨q, t⟩
  simp

theorem bell_mul_conjTranspose : bell * bellᴴ = 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pauli]

theorem bell_conjTranspose_mul : bellᴴ * bell = 1 := by
  ext ⟨q, t⟩ ⟨q', t'⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_bell_apply]
  fin_cases q <;> fin_cases t <;> fin_cases q' <;> fin_cases t' <;>
    norm_num [Fintype.sum_prod_type, pauli]

/-- The two halves of a Bell pair have the same basis index. -/
noncomputable def eprAmplitude (t c : Fin 2) : ℂ :=
  if t = c then invSqrtTwo else 0

/-- On input basis state `q`, the Bell transform and an EPR pair give amplitude
`P_key[c,q]/2` for the key and remote basis state `c`. -/
theorem bell_teleport_amplitude (key : Bool × Bool) (c q : Fin 2) :
    (∑ t, bell key (q, t) * eprAmplitude t c) = (2 : ℂ)⁻¹ * pauli key c q := by
  rw [Finset.sum_eq_single c]
  · simp [eprAmplitude, mul_right_comm]
  · intro t _ ht
    simp [eprAmplitude, ht]
  · simp

/-- Inverting the Bell transform restores the local input and the Bell pair. -/
theorem bell_decode_amplitude (q t c input : Fin 2) :
    (∑ key, star (bell key (q, t)) * ((2 : ℂ)⁻¹ * pauli key c input)) =
      if q = input then eprAmplitude t c else 0 := by
  have h (key : Bool × Bool) :
      bell key (input, c) * invSqrtTwo = (2 : ℂ)⁻¹ * pauli key c input := by
    rw [bell_apply, mul_right_comm, invSqrtTwo_mul_self]
  calc
    _ = ∑ key, (star (bell key (q, t)) * bell key (input, c)) * invSqrtTwo := by
      apply Finset.sum_congr rfl
      intro key _
      rw [mul_assoc, h]
    _ = (bellᴴ * bell) (q, t) (input, c) * invSqrtTwo := by
      rw [Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.conjTranspose_apply]
    _ = _ := by
      rw [bell_conjTranspose_mul]
      by_cases h : q = input <;> simp [Matrix.one_apply, eprAmplitude, h]

/-- Removing the known Pauli pad leaves the original input amplitude. -/
theorem pauli_decode_amplitude (key : Bool × Bool) (q input : Fin 2) :
    (∑ c, star (pauli key c q) * ((2 : ℂ)⁻¹ * pauli key c input)) =
      if q = input then (2 : ℂ)⁻¹ else 0 := by
  calc
    _ = (2 : ℂ)⁻¹ * ((pauli key)ᴴ * pauli key) q input := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Matrix.conjTranspose_apply, mul_left_comm]
    _ = _ := by
      rw [pauli_conjTranspose_mul]
      by_cases h : q = input <;> simp [Matrix.one_apply, h]

end LinearRouting.ExactPhase
