import LinearRouting.BipartiteDensity

/-!
# Copied outcome registers in the receiver marginals

When both receivers have a copy of each outcome, tracing one receiver
eliminates coherences between different flags in the other receiver's state.
-/

namespace LinearRouting.ExactPhase

open Matrix

variable {I B A F : Type*} [Fintype I]

private theorem copiedFlags_joint_zero
    (G : Matrix (B × A) I ℂ) (flagB : B → F) (flagA : A → F)
    (hG : ∀ b a q, flagB b ≠ flagA a → G (b, a) q = 0)
    (Q : Matrix I I ℂ) (b b' : B) (a a' : A)
    (h : flagB b ≠ flagA a ∨ flagB b' ≠ flagA a') :
    (G * Q * Gᴴ) (b, a) (b', a') = 0 := by
  rcases h with h | h
  · have hz (q : I) : G (b, a) q = 0 := hG b a q h
    simp [Matrix.mul_apply, hz]
  · have hz (q : I) : G (b', a') q = 0 := hG b' a' q h
    simp [Matrix.mul_apply, hz]

/-- Bob's state is block diagonal in the copied flags. -/
theorem bobMarginal_zero_of_flag_ne [Fintype A]
    (G : Matrix (B × A) I ℂ) (flagB : B → F) (flagA : A → F)
    (hG : ∀ b a q, flagB b ≠ flagA a → G (b, a) q = 0)
    (Q : Matrix I I ℂ) (b b' : B) (h : flagB b ≠ flagB b') :
    environmentPartialTrace B A (G * Q * Gᴴ) b b' = 0 := by
  rw [environmentPartialTrace_apply]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  apply copiedFlags_joint_zero G flagB flagA hG
  by_cases he : flagB b = flagA a
  · exact Or.inr fun he' ↦ h (he.trans he'.symm)
  · exact Or.inl he

/-- Alice's state is block diagonal in the copied flags. -/
theorem aliceMarginal_zero_of_flag_ne [Fintype B]
    (G : Matrix (B × A) I ℂ) (flagB : B → F) (flagA : A → F)
    (hG : ∀ b a q, flagB b ≠ flagA a → G (b, a) q = 0)
    (Q : Matrix I I ℂ) (a a' : A) (h : flagA a ≠ flagA a') :
    firstFactorPartialTrace B A (G * Q * Gᴴ) a a' = 0 := by
  rw [firstFactorPartialTrace_apply]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  apply copiedFlags_joint_zero G flagB flagA hG
  by_cases he : flagB b = flagA a
  · exact Or.inr fun he' ↦ h (he.symm.trans he')
  · exact Or.inl he

end LinearRouting.ExactPhase
