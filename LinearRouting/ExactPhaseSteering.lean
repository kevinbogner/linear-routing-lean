import LinearRouting.ExactPhaseBase
import LinearRouting.Walsh

/-!
# Measurements for the exact phase router

The rows of each measurement matrix are indexed by its classical outcomes.
Alice uses the binary Fourier basis. Bob translates the address in the
role-one branch and then measures the role in the Hadamard basis.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

noncomputable section

/-- The real Walsh character of an address, regarded as a complex amplitude. -/
def addressSign {n : ℕ} (ℓ j : Address n) : ℂ := (walsh n ℓ j : ℂ)

/-- The sign of a Hadamard entry on the role bit before normalization. -/
def roleSign (v r : Bool) : ℂ := if r then bitSign v else 1

@[simp] theorem roleSign_false (v : Bool) : roleSign v false = 1 := rfl

@[simp] theorem roleSign_true (v : Bool) : roleSign v true = bitSign v := rfl

@[simp] theorem star_roleSign (v r : Bool) : star (roleSign v r) = roleSign v r := by
  cases r <;> simp

@[simp] theorem star_addressSign {n : ℕ} (ℓ j : Address n) :
    star (addressSign ℓ j) = addressSign ℓ j := by
  simp [addressSign]

@[simp] theorem addressSign_mul_self {n : ℕ} (ℓ j : Address n) :
    addressSign ℓ j * addressSign ℓ j = 1 := by
  unfold addressSign
  rcases walsh_apply_eq_one_or_eq_neg_one ℓ j with h | h <;>
    rw [h] <;> norm_num

theorem addressSign_add_right {n : ℕ} (ℓ a y : Address n) :
    addressSign ℓ (a + y) = addressSign ℓ a * addressSign ℓ y := by
  simp only [addressSign, walsh_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    chi_add, Complex.ofReal_mul]

/-- The Fourier normalization for a role bit and a binary address. -/
def normalization (n : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ (n + 1))) : ℂ)⁻¹

/-- The one-qubit Hadamard normalization in Bob's measurement. -/
def steerNormalization : ℂ := ((Real.sqrt 2) : ℂ)⁻¹

@[simp] theorem star_normalization (n : ℕ) : star (normalization n) = normalization n := by
  simp [normalization]

@[simp] theorem star_steerNormalization : star steerNormalization = steerNormalization := by
  simp [steerNormalization]

theorem normalization_mul_self (n : ℕ) :
    normalization n * normalization n = ((2 : ℂ) ^ (n + 1))⁻¹ := by
  rw [← pow_two]
  unfold normalization
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_pow]
  norm_num

theorem steerNormalization_mul_self :
    steerNormalization * steerNormalization = (2 : ℂ)⁻¹ := by
  rw [← pow_two]
  unfold steerNormalization
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Alice's normalized Fourier transform, with outcome `(v, ℓ)` in each row. -/
def fourier (n : ℕ) : Matrix (Label n) (Label n) ℂ :=
  Matrix.of fun p q => normalization n * roleSign p.1 q.1 * addressSign p.2 q.2

theorem fourier_entry {n : ℕ} (v r : Bool) (ℓ j : Address n) :
    fourier n (v, ℓ) (r, j) = normalization n * roleSign v r * addressSign ℓ j := rfl

@[simp] theorem star_fourier {n : ℕ} (p q : Label n) :
    star (fourier n p q) = fourier n p q := by
  simp [fourier, star_mul, mul_comm]

/-- Bob's measurement in the signed two-term basis, with outcome `(u, a)` in
each row. -/
def steer {n : ℕ} (y : Address n) : Matrix (Label n) (Label n) ℂ :=
  Matrix.of fun p q =>
    if q.2 = (if q.1 then p.2 + y else p.2) then
      steerNormalization * roleSign p.1 q.1
    else 0

@[simp] theorem steer_false {n : ℕ} (y a j : Address n) (u : Bool) :
    steer y (u, a) (false, j) = if j = a then steerNormalization else 0 := by
  simp [steer]

@[simp] theorem steer_true {n : ℕ} (y a j : Address n) (u : Bool) :
    steer y (u, a) (true, j) =
      if j = a + y then steerNormalization * bitSign u else 0 := by
  simp [steer]

@[simp] theorem steer_false_same {n : ℕ} (y a : Address n) (u : Bool) :
    steer y (u, a) (false, a) = steerNormalization := by simp

@[simp] theorem steer_true_shift {n : ℕ} (y a : Address n) (u : Bool) :
    steer y (u, a) (true, a + y) = steerNormalization * bitSign u := by simp

@[simp] theorem star_steer {n : ℕ} (y : Address n) (p q : Label n) :
    star (steer y p q) = steer y p q := by
  rcases p with ⟨u, a⟩
  rcases q with ⟨r, j⟩
  cases r
  · rw [steer_false]
    split <;> simp
  · rw [steer_true]
    split <;> simp [star_mul, mul_comm]

private theorem role_overlap (u v : Bool) :
    (∑ r : Bool, roleSign u r * roleSign v r) = if u = v then 2 else 0 := by
  cases u <;> cases v <;> norm_num [Fintype.sum_bool]

private theorem address_overlap {n : ℕ} (ℓ k : Address n) :
    (∑ j : Address n, addressSign ℓ j * addressSign k j) =
      if ℓ = k then (2 : ℂ) ^ n else 0 := by
  have h := congrArg (fun M : Matrix (Address n) (Address n) ℝ => M ℓ k)
    (walsh_mul_transpose n)
  rw [Matrix.mul_apply] at h
  have hc := congrArg Complex.ofReal h
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at hc
  by_cases hEq : ℓ = k <;>
    simpa [addressSign, hEq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using hc

/-- The rows of Alice's Fourier transform form an orthonormal basis. -/
theorem fourier_coisometry (n : ℕ) : fourier n * (fourier n)ᴴ = 1 := by
  ext ⟨u, ℓ⟩ ⟨v, k⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_fourier,
    Fintype.sum_prod_type, fourier_entry]
  calc
    _ = (normalization n * normalization n) *
        (∑ r : Bool, roleSign u r * roleSign v r) *
        (∑ j : Address n, addressSign ℓ j * addressSign k j) := by
      have h :
          (normalization n * normalization n) * (∑ r : Bool, roleSign u r * roleSign v r) =
            ∑ r : Bool, (normalization n * normalization n) * (roleSign u r * roleSign v r) :=
        Finset.mul_sum _ _ _
      rw [h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [role_overlap, address_overlap, normalization_mul_self]
      by_cases huv : u = v <;> by_cases hℓk : ℓ = k
      · subst v
        subst k
        rw [if_pos rfl, if_pos rfl, Matrix.one_apply_eq, mul_assoc, mul_comm (2 : ℂ),
          ← pow_succ]
        exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
      · simp [huv, hℓk]
      · simp [huv, hℓk]
      · simp [huv, hℓk]

/-- Alice's Fourier transform preserves inner products. -/
theorem fourier_isometry (n : ℕ) : (fourier n)ᴴ * fourier n = 1 :=
  mul_eq_one_comm.mp (fourier_coisometry n)

/-- The rows of Bob's steering matrix form an orthonormal basis. -/
theorem steer_coisometry {n : ℕ} (y : Address n) : steer y * (steer y)ᴴ = 1 := by
  ext ⟨u, a⟩ ⟨v, b⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_steer,
    Fintype.sum_prod_type, Fintype.sum_bool, steer_false, steer_true]
  by_cases hab : a = b
  · subst b
    cases u <;> cases v <;>
      simp [ite_mul, mul_ite] <;>
      rw [steerNormalization_mul_self] <;> norm_num
  · have hab' : a + y ≠ b + y := fun h => hab (add_right_cancel h)
    have hterm (j : Address n) (c d : Address n) (hcd : c ≠ d) (s t : ℂ) :
        (if j = c then s else 0) * (if j = d then t else 0) = 0 := by
      by_cases hj : j = c
      · simp [hj, hcd]
      · simp [hj]
    simp [hterm _ a b hab, hterm _ (a + y) (b + y) hab', hab]

/-- Bob's steering measurement is complete. -/
theorem steer_isometry {n : ℕ} (y : Address n) : (steer y)ᴴ * steer y = 1 :=
  mul_eq_one_comm.mp (steer_coisometry y)

/-- Multiplying the measurement amplitudes and summing out the shared label
leaves precisely the two translated branches and their relative sign. -/
theorem steer_fourier_combination {n : ℕ} (y a ℓ : Address n) (u v : Bool)
    (w : Label n → ℂ) :
    (∑ p : Label n, (fourier n (v, ℓ) p * steer y (u, a) p) * w p) =
      (normalization n * steerNormalization * addressSign ℓ a) *
        (w (false, a) + (bitSign u * bitSign v * addressSign ℓ y) * w (true, a + y)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, fourier_entry, steer_false, steer_true,
    roleSign_false, roleSign_true, mul_one, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, addressSign_add_right]
  ring

end

end LinearRouting.ExactPhase
