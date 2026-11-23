import LinearRouting.ExactPhaseLocal
import LinearRouting.ExactPhaseSteering
import LinearRouting.ExactPhaseWork

/-!
# Conditional work amplitudes

The two measured labels determine the sign in the work superposition.
Alice undoes the resulting orthogonal operation or Bob uses its spectral
support, according to the routing bit.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The two role outcomes and the address Fourier phase give this flag bit. -/
def flagPhase (y : Address n) (h g : Label n) : Bool :=
  (g.1 ^^ h.1) ^^ decide ((∑ i, h.2 i * y i) = (1 : ZMod 2))

theorem bitSign_flagPhase (y : Address n) (h g : Label n) :
    bitSign (flagPhase y h g) = bitSign g.1 * bitSign h.1 * addressSign h.2 y := by
  have hchar : ∀ w : ZMod 2, bitSign (decide (w = 1)) = (chi w : ℂ) := by
    intro w
    have hw : w = 0 ∨ w = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) w
    rcases hw with rfl | rfl <;> simp
  rw [flagPhase, bitSign_xor, bitSign_xor, hchar, addressSign, walsh_apply]

/-- The conditional work amplitude, including its flag-dependent sign. -/
def outcomeMix (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) : Matrix (Work n) (Work n) ℂ :=
  workMix row g.2 (g.2 + y) (flagPhase y h g ^^ z)

/-- The common scalar from the Fourier outcome and the local work pair. -/
def outcomeScale (h g : Label n) : ℂ :=
  normalization n * flatAmplitude (Fintype.card (Work n)) * addressSign h.2 g.2

theorem gadget_contraction (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) (p p' : Work n) :
    (∑ j : Label n,
      localGadget (fourier n) (phaseWorkOperator row z) (h, p, p') j * steer y g j) =
      outcomeScale h g * outcomeMix row y h g z p p' := by
  rcases h with ⟨v, ℓ⟩
  rcases g with ⟨u, a⟩
  calc
    _ = ∑ j : Label n, (fourier n (v, ℓ) j * steer y (u, a) j) *
        (flatAmplitude (Fintype.card (Work n)) * phaseWorkOperator row z j p p') := by
      apply Finset.sum_congr rfl
      intro j _
      unfold localGadget
      ring
    _ = _ := by
      rw [steer_fourier_combination]
      simp only [outcomeScale, outcomeMix, workMix_apply, bitSign_xor, bitSign_flagPhase,
        phaseWorkOperator, Bool.false_eq_true, if_false, if_true,
        Matrix.smul_apply, smul_eq_mul]
      rw [show steerNormalization = invSqrtTwo from rfl]
      ring

private theorem add_self_add (a y : Address n) : a + (a + y) = y := by
  funext i
  change a i + (a i + y i) = y i
  rw [← add_assoc, (by decide : ∀ z : ZMod 2, z + z = 0), zero_add]

theorem outcomeMix_false_isometry (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) (hy : row y = false) :
    (outcomeMix row y h g z)ᴴ * outcomeMix row y h g z = 1 := by
  rw [outcomeMix, workMix_conjTranspose]
  exact workMix_false_mul_self _ _ _ _ (by simpa [add_self_add] using hy)

theorem outcomeMix_false_transpose_mul (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) (hy : row y = false) :
    (outcomeMix row y h g z)ᵀ * outcomeMix row y h g z = 1 := by
  rw [outcomeMix, workMix_transpose]
  exact workMix_false_mul_self _ _ _ _ (by simpa [add_self_add] using hy)

theorem outcomeMix_false_mul_transpose (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) (hy : row y = false) :
    outcomeMix row y h g z * (outcomeMix row y h g z)ᵀ = 1 := by
  rw [outcomeMix, workMix_transpose]
  exact workMix_false_mul_self _ _ _ _ (by simpa [add_self_add] using hy)

/-- The work projector corresponding to a decoded key bit. -/
def outcomeProjector (row : Address n → Bool) (y : Address n)
    (h g : Label n) (key : Bool) : Matrix (Work n) (Work n) ℂ :=
  workProjector row g.2 (g.2 + y) (flagPhase y h g ^^ key)

theorem outcomeProjector_sum (row : Address n → Bool) (y : Address n) (h g : Label n) :
    ∑ key : Bool, outcomeProjector row y h g key = 1 := by
  have hsum := workProjector_sum row g.2 (g.2 + y)
  rw [Fintype.sum_bool] at hsum ⊢
  cases hflag : flagPhase y h g <;> simpa [outcomeProjector, hflag, add_comm] using hsum

theorem outcomeProjector_conjTranspose (row : Address n → Bool) (y : Address n)
    (h g : Label n) (key : Bool) (hy : row y = true) :
    (outcomeProjector row y h g key)ᴴ = outcomeProjector row y h g key := by
  exact workProjector_conjTranspose _ _ _ _ (by simpa [add_self_add] using hy)

private theorem xor_left_eq_iff (flag key z : Bool) :
    (flag ^^ key) = (flag ^^ z) ↔ key = z := by
  cases flag <;> cases key <;> cases z <;> decide

theorem outcomeProjector_mul (row : Address n → Bool) (y : Address n) (h g : Label n)
    (key key' : Bool) (hy : row y = true) :
    outcomeProjector row y h g key * outcomeProjector row y h g key' =
      if key = key' then outcomeProjector row y h g key else 0 := by
  simp only [outcomeProjector]
  rw [workProjector_mul _ _ _ _ _ (by simpa [add_self_add] using hy)]
  simp only [xor_left_eq_iff]

theorem outcomeProjector_mul_outcomeMix (row : Address n → Bool) (y : Address n)
    (h g : Label n) (key z : Bool) (hy : row y = true) :
    outcomeProjector row y h g key * outcomeMix row y h g z =
      if key = z then outcomeMix row y h g z else 0 := by
  simp only [outcomeProjector, outcomeMix]
  rw [workProjector_mul_workMix _ _ _ _ _ (by simpa [add_self_add] using hy)]
  simp only [xor_left_eq_iff]

end

end LinearRouting.ExactPhase
