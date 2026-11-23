import Mathlib.Data.ZMod.Basic
import LinearRouting.FiniteKraus

/-!
# Basis labels for the exact phase router
-/

namespace LinearRouting.ExactPhase

/-- Addresses and inputs are binary strings of the same length. -/
abbrev Address (n : ℕ) := Fin n → ZMod 2

/-- A resource label consists of a role bit and an address. -/
abbrev Label (n : ℕ) := Bool × Address n

/-- The basis of a workspace with one qubit per address. -/
abbrev Work (n : ℕ) := Address n → ZMod 2

/-- The two resource labels on either side of the cut. -/
abbrev Source (n : ℕ) := Label n × Label n

/-- The sign implemented by a binary phase gate. -/
def bitSign (z : Bool) : ℂ := if z then -1 else 1

@[simp] theorem bitSign_false : bitSign false = 1 := rfl
@[simp] theorem bitSign_true : bitSign true = -1 := rfl

@[simp] theorem bitSign_mul_self (z : Bool) : bitSign z * bitSign z = 1 := by
  cases z <;> simp

@[simp] theorem star_bitSign (z : Bool) : star (bitSign z) = bitSign z := by
  cases z <;> simp

theorem bitSign_xor (z w : Bool) : bitSign (z ^^ w) = bitSign z * bitSign w := by
  cases z <;> cases w <;> simp

theorem card_label (n : ℕ) : Fintype.card (Label n) = 2 ^ (n + 1) := by
  simp [Label, Address, ZMod.card, pow_succ, Nat.mul_comm]

/-- A pair of role-address registers on each side is the basis of
\(2n+2\) qubits on that side. -/
theorem card_source (n : ℕ) : Fintype.card (Source n) = 2 ^ (2 * n + 2) := by
  rw [Fintype.card_prod, card_label, ← pow_add]
  congr 1
  omega

/-- A real amplitude in a maximally entangled state of local dimension \(d\). -/
noncomputable def flatAmplitude (d : ℕ) : ℂ :=
  (Real.sqrt ((d : ℝ)⁻¹) : ℝ)

@[simp] theorem star_flatAmplitude (d : ℕ) : star (flatAmplitude d) = flatAmplitude d := by
  simp [flatAmplitude]

theorem flatAmplitude_mul_self (d : ℕ) :
    flatAmplitude d * flatAmplitude d = (d : ℂ)⁻¹ := by
  have h := Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg d : (0 : ℝ) ≤ d))
  unfold flatAmplitude
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using
    congrArg Complex.ofReal h

theorem flatAmplitude_mul_self_mul_card {d : ℕ} (hd : d ≠ 0) :
    flatAmplitude d * flatAmplitude d * (d : ℂ) = 1 := by
  rw [flatAmplitude_mul_self, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd)]

end LinearRouting.ExactPhase
