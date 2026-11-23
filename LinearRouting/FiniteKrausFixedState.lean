import LinearRouting.DensityPurification

/-!
# Appending a fixed finite density matrix

This file constructs the channel that adjoins an arbitrary fixed density
matrix to an otherwise unchanged finite input.  Its Kraus operators are the
environment slices of the canonical purification of the fixed state.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

namespace FiniteKrausChannel

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {n : ℕ}

/-- The Kraus operator indexed by one purifying-environment basis element.
It acts as the identity on `I` and prepares the corresponding purification
slice on the appended `Fin n` factor. -/
noncomputable def appendFixedStateKraus
    (rho : DensityMatrix n) (e : Fin n) : Matrix (I × Fin n) I ℂ :=
  fun p i ↦ if p.1 = i then purificationVector rho (p.2, e) else 0

private theorem appendFixedStateKraus_completeness
    (rho : DensityMatrix n) :
    ∑ e, (appendFixedStateKraus (I := I) rho e)ᴴ *
      appendFixedStateKraus (I := I) rho e = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, appendFixedStateKraus,
      Matrix.one_apply, ↓reduceIte]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos]
      rw [Finset.sum_comm]
      rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n ↦
        star (purificationVector rho p) * purificationVector rho p)]
      simpa [dotProduct] using purificationVector_normalized rho
    · intro j _hj hji
      simp [hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, appendFixedStateKraus,
      Matrix.one_apply, hij, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro e _he
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hpi : p.1 = i
    · simp [hpi, hij]
    · simp [hpi]

/-- The finite Kraus channel `Q ↦ Q ⊗ₖ rho.val`. -/
noncomputable def appendFixedState (rho : DensityMatrix n) :
    FiniteKrausChannel (Fin n) I (I × Fin n) where
  kraus := appendFixedStateKraus rho
  completeness := appendFixedStateKraus_completeness rho

@[simp]
theorem appendFixedState_kraus (rho : DensityMatrix n) (e : Fin n) :
    (appendFixedState (I := I) rho).kraus e =
      appendFixedStateKraus rho e := rfl

/-- Appending the fixed state has the expected tensor-product action on every
input matrix, not only on density matrices. -/
theorem appendFixedState_action (rho : DensityMatrix n)
    (Q : Matrix I I ℂ) :
    (appendFixedState rho).action Q = Q ⊗ₖ rho.val := by
  classical
  ext p q
  simp only [action_apply, Matrix.sum_apply, Matrix.mul_apply,
    appendFixedState_kraus, appendFixedStateKraus,
    Matrix.conjTranspose_apply]
  change (∑ e,
      ∑ j,
        (∑ i, (if p.1 = i then purificationVector rho (p.2, e) else 0) *
          Q i j) *
          star (if q.1 = j then purificationVector rho (q.2, e) else 0)) =
    Q p.1 q.1 * rho.val p.2 q.2
  simp only [ite_mul, zero_mul]
  simp [Finset.sum_ite_eq]
  have hmarg := congrFun (congrFun
    (environmentPartialTrace_purificationPureMatrix rho) p.2) q.2
  simp only [environmentPartialTrace_apply, purificationPureMatrix,
    Matrix.vecMulVec_apply, Pi.star_apply] at hmarg
  have hj_sum (e : Fin n) :
      (∑ j, purificationVector rho (p.2, e) * Q p.1 j *
        star (if q.1 = j then purificationVector rho (q.2, e) else 0)) =
        purificationVector rho (p.2, e) * Q p.1 q.1 *
          star (purificationVector rho (q.2, e)) := by
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro j _hj hjq
      simp [Ne.symm hjq]
    · intro hq
      exact (hq (Finset.mem_univ q.1)).elim
  calc
    (∑ e, ∑ j, purificationVector rho (p.2, e) * Q p.1 j *
        star (if q.1 = j then purificationVector rho (q.2, e) else 0)) =
        ∑ e, purificationVector rho (p.2, e) * Q p.1 q.1 *
          star (purificationVector rho (q.2, e)) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact hj_sum e
    _ = Q p.1 q.1 *
        ∑ e, purificationVector rho (p.2, e) *
          star (purificationVector rho (q.2, e)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ = Q p.1 q.1 * rho.val p.2 q.2 := by rw [hmarg]

end FiniteKrausChannel

end LinearRouting
