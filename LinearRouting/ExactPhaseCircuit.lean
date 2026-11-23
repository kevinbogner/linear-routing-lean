import LinearRouting.ExactPhaseOutcome
import LinearRouting.ExactPhaseClassicalFlags
import LinearRouting.SchmidtProtocolGlobalChannel

/-!
# The first round of the exact phase router

The local isometries use two role-address sources. The entry formula for the
complete isometry identifies the two conditioned work matrices explicitly.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators Kronecker

set_option maxSynthPendingDepth 12
set_option synthInstance.maxSize 512

noncomputable section

variable {n : ℕ}

abbrev PhaseAlice (n : ℕ) := AliceKeep (Label n) (Work n) × Source n
abbrev PhaseBob (n : ℕ) := AliceSend (Label n) (Work n) × Source n
abbrev SourceDim (n : ℕ) := 2 ^ (2 * n + 2)

def sourceBasis (n : ℕ) : Fin (SourceDim n) ≃ Source n :=
  (Fintype.equivFinOfCardEq (card_source n)).symm

/-- Uniform Schmidt weights for two role-address states. -/
def sourceWeights (n : ℕ) (_ : Fin (SourceDim n)) : ℝ := (SourceDim n : ℝ)⁻¹

theorem sourceWeights_nonnegative (n : ℕ) (j : Fin (SourceDim n)) :
    0 ≤ sourceWeights n j := inv_nonneg.mpr (Nat.cast_nonneg _)

theorem sourceWeights_sum (n : ℕ) : ∑ j, sourceWeights n j = 1 := by
  simp only [sourceWeights, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  apply mul_inv_cancel₀
  exact Nat.cast_ne_zero.mpr (by unfold SourceDim; positivity)

def phaseAlice (f : Address n → Address n → Bool) (x : Address n) :
    Matrix (AliceKeep (Label n) (Work n) × AliceSend (Label n) (Work n))
      (Fin 2 × Fin (SourceDim n)) ℂ :=
  fun o i ↦ aliceEncoder (fourier n) (phaseWorkOperator (f x)) o
    (i.1, sourceBasis n i.2)

def phaseBob (y : Address n) :
    Matrix (Source n × Source n) (Fin (SourceDim n)) ℂ :=
  fun o i ↦ bobEncoder (steer y) o (sourceBasis n i)

theorem phaseAlice_isometry (f : Address n → Address n → Bool) (x : Address n) :
    (phaseAlice f x)ᴴ * phaseAlice f x = 1 := by
  ext ⟨i, l⟩ ⟨j, r⟩
  have h := congr_fun₂
    (aliceEncoder_isometry (fourier n) (fourier_isometry n)
      (phaseWorkOperator (f x)) (phaseWorkOperator_conjTranspose_mul (f x)))
    (i, sourceBasis n l) (j, sourceBasis n r)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseAlice, Matrix.one_apply]
    using h

theorem phaseBob_isometry (y : Address n) : (phaseBob y)ᴴ * phaseBob y = 1 := by
  ext i j
  have h := congr_fun₂ (bobEncoder_isometry (steer y) (steer_isometry y))
    (sourceBasis n i) (sourceBasis n j)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseBob, Matrix.one_apply]
    using h

/-- The two parties' first-round outputs, with Bob's receiver first. -/
def phaseGlobal (f : Address n → Address n → Bool) (x y : Address n) :
    Matrix (PhaseBob n × PhaseAlice n) (Fin 2) ℂ :=
  schmidtProtocolGlobalIsometry (sourceWeights n) (phaseAlice f) phaseBob x y

theorem phaseGlobal_isometry (f : Address n → Address n → Bool) (x y : Address n) :
    (phaseGlobal f x y)ᴴ * phaseGlobal f x y = 1 :=
  schmidtProtocolGlobalIsometry_isometry (sourceWeights n)
    (sourceWeights_nonnegative n) (sourceWeights_sum n)
    (phaseAlice f) phaseBob (phaseAlice_isometry f) phaseBob_isometry x y

def globalScale (h g : Source n) : ℂ :=
  flatAmplitude (SourceDim n) * outcomeScale h.1 g.1 * outcomeScale h.2 g.2

private theorem sum_pair_product {L : Type*} [Fintype L] (a b : L → ℂ) (c : ℂ) :
    (∑ j : L × L, c * (a j.1 * b j.2)) = c * (∑ i, a i) * ∑ j, b j := by
  rw [Fintype.sum_prod_type, Finset.mul_sum Finset.univ a c, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Expand the tensor product of the two local maps on the shared EPR source.
The receiver indices include both copies of each outcome. -/
theorem phaseGlobal_apply (f : Address n → Address n → Bool) (x y : Address n)
    (c q : Fin 2) (k : Key) (p p' : Pair (Work n))
    (h h' g g' : Source n) :
    phaseGlobal f x y ((((c, p), h), g), (((k, p'), h'), g')) q =
      if h' = h ∧ g = g' then
        globalScale h g * ((2 : ℂ)⁻¹ * pauli k c q *
          outcomeMix (f x) y h.1 g.1 k.1 p.1 p'.1 *
          outcomeMix (f x) y h.2 g.2 k.2 p.2 p'.2) else 0 := by
  rw [phaseGlobal, schmidtProtocolGlobalIsometry_apply]
  simp only [phaseAlice, phaseBob, sourceWeights, aliceEncoder_apply,
    bobEncoder]
  by_cases ha : h' = h <;> by_cases hb : g = g' <;> simp only [ha, hb,
    if_true, if_false, true_and, false_and, and_false, zero_mul, mul_zero,
    Finset.sum_const_zero]
  subst h'
  subst g'
  let a (j : Label n) :=
    localGadget (fourier n) (phaseWorkOperator (f x) k.1) (h.1, p.1, p'.1) j * steer y g.1 j
  let b (j : Label n) :=
    localGadget (fourier n) (phaseWorkOperator (f x) k.2) (h.2, p.2, p'.2) j * steer y g.2 j
  let C := flatAmplitude (SourceDim n) * ((2 : ℂ)⁻¹ * pauli k c q)
  calc
    _ = ∑ j : Fin (SourceDim n),
        C * (a (sourceBasis n j).1 * b (sourceBasis n j).2) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [a, b, C, flatAmplitude, Matrix.kroneckerMap_apply]
      ring
    _ = ∑ j : Source n, C * (a j.1 * b j.2) :=
      Equiv.sum_comp (sourceBasis n) (fun j ↦ C * (a j.1 * b j.2))
    _ = _ := by
      rw [sum_pair_product]
      dsimp only [a, b, C]
      rw [gadget_contraction, gadget_contraction]
      unfold globalScale
      ring

/-- Nonzero first-round amplitudes have agreeing copies of each outcome. -/
theorem phaseGlobal_flags_match (f : Address n → Address n → Bool)
    (x y : Address n) (b : PhaseBob n) (a : PhaseAlice n) (q : Fin 2)
    (h : (b.1.2, b.2) ≠ (a.1.2, a.2)) :
    phaseGlobal f x y (b, a) q = 0 := by
  rcases b with ⟨⟨⟨c, p⟩, hb⟩, gb⟩
  rcases a with ⟨⟨⟨k, p'⟩, ha⟩, ga⟩
  rw [phaseGlobal_apply, if_neg]
  intro he
  exact h (Prod.ext he.1.symm he.2)

/-- Coherently copying the two outcomes gives a classical flag in Alice's
receiver marginal. -/
theorem phaseAlice_flags_classical (f : Address n → Address n → Bool)
    (x y : Address n) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a a' : PhaseAlice n) (h : (a.1.2, a.2) ≠ (a'.1.2, a'.2)) :
    firstFactorPartialTrace (PhaseBob n) (PhaseAlice n)
      (phaseGlobal f x y * Q * (phaseGlobal f x y)ᴴ) a a' = 0 :=
  aliceMarginal_zero_of_flag_ne (phaseGlobal f x y)
    (fun b ↦ (b.1.2, b.2)) (fun a ↦ (a.1.2, a.2))
    (phaseGlobal_flags_match f x y) Q a a' h

/-- Coherently copying the two outcomes gives a classical flag in Bob's
receiver marginal. -/
theorem phaseBob_flags_classical (f : Address n → Address n → Bool)
    (x y : Address n) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (b b' : PhaseBob n) (h : (b.1.2, b.2) ≠ (b'.1.2, b'.2)) :
    environmentPartialTrace (PhaseBob n) (PhaseAlice n)
      (phaseGlobal f x y * Q * (phaseGlobal f x y)ᴴ) b b' = 0 :=
  bobMarginal_zero_of_flag_ne (phaseGlobal f x y)
    (fun b ↦ (b.1.2, b.2)) (fun a ↦ (a.1.2, a.2))
    (phaseGlobal_flags_match f x y) Q b b' h

end

end LinearRouting.ExactPhase
