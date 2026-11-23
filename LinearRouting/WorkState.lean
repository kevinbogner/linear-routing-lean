import LinearRouting.ExactPhaseWork

/-!
# Normalization of the one-block work state

The vector obtained by applying a work operator to half of the local
maximally entangled pair has squared norm given by the operator's normalized
Hilbert–Schmidt norm.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators Kronecker

variable {n : ℕ}

/-- The amplitude of `(V ⊗ I) Ω` in the basis of the two work registers. -/
noncomputable def workPairAmplitude
    (V : Matrix (Work n) (Work n) ℂ) (w : Work n × Work n) : ℂ :=
  flatAmplitude (Fintype.card (Work n)) * V w.1 w.2

/-- Applying the operator to the first half of the local entangled pair
gives the stated entry formula. -/
theorem workPairAmplitude_eq_kronecker_mulVec (V : Matrix (Work n) (Work n) ℂ)
    (w : Work n × Work n) :
    ((V ⊗ₖ (1 : Matrix (Work n) (Work n) ℂ)) *ᵥ fun p ↦
      if p.1 = p.2 then flatAmplitude (Fintype.card (Work n)) else 0) w =
      workPairAmplitude V w := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp [workPairAmplitude, mul_comm]

private theorem sum_workPair_normSq_eq_trace (V : Matrix (Work n) (Work n) ℂ) :
    ((∑ w, Complex.normSq (workPairAmplitude V w) : ℝ) : ℂ) =
      (flatAmplitude (Fintype.card (Work n)) * flatAmplitude (Fintype.card (Work n))) *
        (Vᴴ * V).trace := by
  rw [Complex.ofReal_sum]
  calc
    _ = ∑ w : Work n × Work n,
        (flatAmplitude (Fintype.card (Work n)) * flatAmplitude (Fintype.card (Work n))) *
          (star (V w.1 w.2) * V w.1 w.2) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, workPairAmplitude, star_mul',
        star_flatAmplitude]
      ring
    _ = _ := by
      rw [← Finset.mul_sum, Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem workMix_trace_conjTranspose_mul (row : Address n → Bool)
    (a b : Address n) (z : Bool) :
    ((workMix row a b z)ᴴ * workMix row a b z).trace = Fintype.card (Work n) := by
  have hcross : (workPhase row b * workFlip a).trace = 0 :=
    (Matrix.trace_mul_comm _ _).trans (work_trace_cross row a b)
  rw [workMix_conjTranspose]
  unfold workMix
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, invSqrtTwo_mul_self]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, workFlip_mul_self, workPhase_mul_self,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one,
    work_trace_cross, hcross, smul_eq_mul, mul_zero, add_zero, zero_add]
  cases z <;> simp only [bitSign_true, bitSign_false] <;> ring

/-- The work vector in the one-block amplitude has norm one in both routing cases. -/
theorem workMix_workPair_normSq (row : Address n → Bool) (a b : Address n)
    (z : Bool) :
    ∑ w, Complex.normSq (workPairAmplitude (workMix row a b z) w) = 1 := by
  apply Complex.ofReal_injective
  rw [sum_workPair_normSq_eq_trace, workMix_trace_conjTranspose_mul, Complex.ofReal_one]
  exact flatAmplitude_mul_self_mul_card Fintype.card_ne_zero

end LinearRouting.ExactPhase
