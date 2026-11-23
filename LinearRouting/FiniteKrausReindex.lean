import LinearRouting.FiniteKraus

/-!
# Finite Kraus basis reindexing

An equivalence of finite basis types is implemented by a permutation
isometry.  The associated one-Kraus channel acts by ordinary matrix
reindexing.  This lets protocol normal-form arguments change between nested
product carriers and standard `Fin` carriers without changing a channel.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

namespace FiniteKrausChannel

universe uI uO

variable {I : Type uI} {O : Type uO}
variable [Fintype I] [DecidableEq I]
variable [Fintype O] [DecidableEq O]

/-- Permutation matrix associated with an equivalence from the input basis
to the output basis. -/
def equivalenceIsometry (e : I ≃ O) : Matrix O I ℂ :=
  fun o i ↦ if o = e i then 1 else 0

omit [Fintype I] in
theorem equivalenceIsometry_conjTranspose_mul (e : I ≃ O) :
    (equivalenceIsometry e)ᴴ * equivalenceIsometry e = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [equivalenceIsometry, Matrix.mul_apply]
  · simp [equivalenceIsometry, Matrix.mul_apply, hij, Ne.symm hij]

/-- The one-Kraus channel implementing a finite basis equivalence. -/
noncomputable def reindex (e : I ≃ O) :
    FiniteKrausChannel (Fin 1) I O :=
  ofIsometry (equivalenceIsometry e)
    (equivalenceIsometry_conjTranspose_mul e)

/-- The reindex channel acts by reindexing both matrix indices along the
supplied equivalence. -/
theorem reindex_action (e : I ≃ O) (M : Matrix I I ℂ) :
    (reindex e).action M = Matrix.reindex e e M := by
  rw [reindex, ofIsometry_action]
  ext o p
  have hsum (q : O) (g : I → ℂ) :
      ∑ i, (if q = e i then g i else 0) = g (e.symm q) := by
    rw [Finset.sum_eq_single (e.symm q)]
    · rw [if_pos (e.apply_symm_apply q).symm]
    · intro i _hi hne
      have hqi : q ≠ e i := by
        intro h
        apply hne
        exact (e.injective ((e.apply_symm_apply q).trans h)).symm
      simp [hqi]
    · intro hq
      exact (hq (Finset.mem_univ _)).elim
  simp only [equivalenceIsometry, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  have hstar (P : Prop) [Decidable P] :
      star (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
    by_cases hP : P <;> simp [hP]
  simp_rw [hstar, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [hsum p, hsum o]

end FiniteKrausChannel

end LinearRouting
