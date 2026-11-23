import LinearRouting.ExactPhaseOutcome
import LinearRouting.WorkState

/-!
# One block after the exchange

The branch indexed by Alice's and Bob's outcomes is the contraction of
their measurement rows against a single shared block. Lemma 3 gives its
amplitude and the norm of its conditional work vector.
-/

namespace LinearRouting.ExactPhase

open Matrix

noncomputable section

variable {n : ℕ}

/-- Amplitudes after the local operations for a fixed pair of outcomes `h`
and `g`. One shared block contributes the amplitude at each matching label
`j`. Alice's gadget applies the controlled work operator to her local work
pair and projects onto `h`. Bob's measurement projects onto `g`. The key
qubit is a control and stays in its input basis state `z`. -/
def blockOutcomeAmplitude (row : Address n → Bool) (y : Address n)
    (h g : Label n) (z : Bool) : Bool × Pair (Work n) → ℂ :=
  fun p ↦ if p.1 = z then
    flatAmplitude (Fintype.card (Label n)) *
      (∑ j : Label n, localGadget (fourier n) (phaseWorkOperator row z)
        (h, p.2.1, p.2.2) j * steer y g j)
  else 0

/-- The matrix `M_z` in the paper, with all additions of bits modulo two. -/
theorem outcomeMix_eq (f : Address n → Address n → Bool) (x y a ℓ : Address n)
    (z u s : Bool) :
    outcomeMix (f x) y (s, ℓ) (u, a) z =
      invSqrtTwo • (workFlip a +
        bitSign (z ^^ ((u ^^ s) ^^ decide ((∑ i, ℓ i * y i) = (1 : ZMod 2)))) •
          workPhase (f x) (a + y)) := by
  unfold outcomeMix workMix
  rw [Bool.xor_comm (flagPhase y (s, ℓ) (u, a)) z]
  rfl

private theorem flatAmplitude_label (n : ℕ) :
    flatAmplitude (Fintype.card (Label n)) = normalization n := by
  rw [flatAmplitude, card_label, normalization, Real.sqrt_inv, Complex.ofReal_inv]
  norm_cast

/-- Lemma 3 of the paper. The branch vector has a fixed key qubit and
the work vector `(M_z ⊗ I) Ω`, with scalar `(-1)^(ℓ·a)/(2·2^n)`.
The work vector has Hilbert norm one for both routing values. -/
theorem oneBlock (f : Address n → Address n → Bool) (x y a ℓ : Address n)
    (z u s : Bool) :
    let M := outcomeMix (f x) y (s, ℓ) (u, a) z
    blockOutcomeAmplitude (f x) y (s, ℓ) (u, a) z =
        (fun p ↦ if p.1 = z then
          (addressSign ℓ a / (2 * (2 : ℂ) ^ n)) * workPairAmplitude M p.2 else 0) ∧
      ‖(WithLp.toLp 2 (workPairAmplitude M) : EuclideanSpace ℂ (Pair (Work n)))‖ = 1 := by
  dsimp only
  constructor
  · funext p
    by_cases hp : p.1 = z
    · rw [blockOutcomeAmplitude, if_pos hp, if_pos hp, gadget_contraction,
        flatAmplitude_label]
      change normalization n * (normalization n * flatAmplitude (Fintype.card (Work n)) *
          addressSign ℓ a * outcomeMix (f x) y (s, ℓ) (u, a) z p.2.1 p.2.2) = _
      rw [show 2 * (2 : ℂ) ^ n = (2 : ℂ) ^ (n + 1) by rw [pow_succ, mul_comm]]
      rw [div_eq_mul_inv, ← normalization_mul_self]
      unfold workPairAmplitude
      ring
    · simp [blockOutcomeAmplitude, hp]
  · rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ w, ‖workPairAmplitude (outcomeMix (f x) y (s, ℓ) (u, a) z) w‖ ^ 2) = 1
    simp only [Complex.sq_norm, outcomeMix, workMix_workPair_normSq, Real.sqrt_one]

end

end LinearRouting.ExactPhase
