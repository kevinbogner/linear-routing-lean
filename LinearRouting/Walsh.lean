import Mathlib

/-!
# Walsh-Hadamard orthogonality

The Walsh-Hadamard matrix supplies the address part of Alice's measurement
basis. Its entry at `(x, y)` is `chi (∑ i, x i * y i)`, where
`chi a = (-1 : ℝ) ^ a.val`. The identity `chi (a + b) = chi a * chi b`
reduces the inner product of two rows to a character sum. If the rows
differ at coordinate `i`, flipping bit `i` pairs terms of opposite signs.
-/

namespace LinearRouting

open Finset Matrix

/-- The sign character of `ZMod 2`, sending `0 ↦ 1` and `1 ↦ -1`. -/
def chi (a : ZMod 2) : ℝ := (-1) ^ a.val

@[simp] lemma chi_zero : chi 0 = 1 := by simp [chi]

@[simp] lemma chi_one : chi 1 = -1 := by
  have h : (1 : ZMod 2).val = 1 := by decide
  simp [chi, h]

/-- `chi` is a character: it turns addition in `ZMod 2` into multiplication. -/
lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  simp only [chi]
  rw [ZMod.val_add, ← pow_add]
  rcases Nat.even_or_odd (a.val + b.val) with hk | hk
  · rw [Nat.even_iff.mp hk, pow_zero, hk.neg_one_pow]
  · rw [Nat.odd_iff.mp hk, pow_one, hk.neg_one_pow]

lemma chi_eq_one_or_eq_neg_one (a : ZMod 2) : chi a = 1 ∨ chi a = -1 := by
  have h : a.val < 2 := ZMod.val_lt a
  have h' : a.val = 0 ∨ a.val = 1 := by omega
  rcases h' with h' | h' <;> simp [chi, h']

/-- The Walsh-Hadamard sign matrix has rows and columns indexed by
`Fin n → ZMod 2`, and the entry at `(x, y)` is `(-1)` raised to the mod-2
inner product of `x` and `y`. -/
def walsh (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  Matrix.of fun x y => chi (∑ i, x i * y i)

@[simp] lemma walsh_apply {n : ℕ} (x y : Fin n → ZMod 2) :
    walsh n x y = chi (∑ i, x i * y i) := rfl

/-- The entries of `walsh` in the raw `(-1) ^ val` form. -/
lemma walsh_apply_pow {n : ℕ} (x y : Fin n → ZMod 2) :
    walsh n x y = (-1 : ℝ) ^ (∑ i, x i * y i : ZMod 2).val := rfl

/-- Character-sum lemma: `∑ y, (-1) ^ ⟨z, y⟩` equals `2 ^ n` when `z = 0` and
vanishes otherwise.  The vanishing case cancels the sum against the involution
`y ↦ y + Pi.single i0 1`, where `z i0 ≠ 0`: the involution flips the sign of
every summand. -/
lemma sum_chi_dotProduct {n : ℕ} (z : Fin n → ZMod 2) :
    ∑ y : Fin n → ZMod 2, chi (∑ i, z i * y i)
      = if z = 0 then (2 ^ n : ℝ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    rw [if_pos rfl]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, chi_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    simp
  · rw [if_neg hz]
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hz
    have hz1 : z i0 = 1 := by
      have hall : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact hall _ (by simpa using hi0)
    set s : Fin n → ZMod 2 := Pi.single i0 1 with hs
    have hflip : ∀ y : Fin n → ZMod 2,
        chi (∑ i, z i * y i) + chi (∑ i, z i * (y + s) i) = 0 := by
      intro y
      have hsplit : ∑ i, z i * (y + s) i
          = (∑ i, z i * y i) + ∑ i, z i * s i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]
      have hone : ∑ i, z i * s i = 1 := by
        rw [hs]
        rw [Finset.sum_eq_single i0
          (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
          (fun hmem => absurd (Finset.mem_univ i0) hmem)]
        rw [Pi.single_eq_same, hz1, mul_one]
      rw [hsplit, hone, chi_add, chi_one, mul_neg_one, add_neg_cancel]
    refine Finset.sum_ninvolution (fun y => y + s) hflip (fun y _ => ?_)
      (fun y => Finset.mem_univ _) (fun y => ?_)
    · intro hcon
      have h1 : y i0 + s i0 = y i0 + 0 := by
        rw [add_zero]
        exact congrFun hcon i0
      have h2 : s i0 = 0 := add_left_cancel h1
      rw [hs, Pi.single_eq_same] at h2
      exact (by decide : (1 : ZMod 2) ≠ 0) h2
    · funext i
      show y i + s i + s i = y i
      rw [add_assoc, (by decide : ∀ a : ZMod 2, a + a = 0) (s i), add_zero]

/-- Taking the inner products of Walsh-Hadamard rows gives `2 ^ n` times the
identity matrix. -/
theorem walsh_mul_transpose (n : ℕ) :
    walsh n * (walsh n)ᵀ = (2 ^ n : ℝ) • 1 := by
  ext x x'
  rw [Matrix.mul_apply]
  have hterm : ∀ y, walsh n x y * (walsh n)ᵀ y x'
      = chi (∑ i, (x + x') i * y i) := by
    intro y
    rw [Matrix.transpose_apply, walsh_apply, walsh_apply, ← chi_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_mul]
  have hsum : ∑ y, walsh n x y * (walsh n)ᵀ y x'
      = ∑ y : Fin n → ZMod 2, chi (∑ i, (x + x') i * y i) :=
    Finset.sum_congr rfl fun y _ => hterm y
  rw [hsum, sum_chi_dotProduct]
  have hcond : x + x' = 0 ↔ x = x' := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ hi
    · rintro rfl
      funext i
      show x i + x i = 0
      exact (by decide : ∀ a : ZMod 2, a + a = 0) _
  rcases eq_or_ne x x' with h | h
  · subst h
    rw [if_pos (hcond.mpr rfl), Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
  · rw [if_neg (fun hc => h (hcond.mp hc)), Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_eq_mul, mul_zero]

/-- The Walsh-Hadamard matrix is symmetric. -/
theorem walsh_transpose (n : ℕ) : (walsh n)ᵀ = walsh n := by
  ext x y
  rw [Matrix.transpose_apply, walsh_apply, walsh_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The symmetric Walsh-Hadamard matrix squares to `2 ^ n` times the identity. -/
theorem walsh_mul_self (n : ℕ) : walsh n * walsh n = (2 ^ n : ℝ) • 1 := by
  have h := walsh_mul_transpose n
  rwa [walsh_transpose] at h

/-- Every entry of the Walsh-Hadamard matrix is a sign. -/
theorem walsh_apply_eq_one_or_eq_neg_one {n : ℕ} (x y : Fin n → ZMod 2) :
    walsh n x y = 1 ∨ walsh n x y = -1 :=
  chi_eq_one_or_eq_neg_one _

end LinearRouting
