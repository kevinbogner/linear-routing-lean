import LinearRouting.BipartiteDensity
import LinearRouting.FiniteKraus

/-!
# Partial trace as a finite Kraus channel

Discarding either factor of a bipartite state is a finite Kraus channel.
Its action on matrices is the partial trace over that factor.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

universe uI uJ

namespace FiniteKrausChannel

variable (I : Type uI) (J : Type uJ)
variable [Fintype I] [DecidableEq I]
variable [Fintype J] [DecidableEq J]

/-- Kraus row that selects the environment basis value `j`. -/
def discardSecondKraus (j : J) : Matrix I (I × J) ℂ :=
  fun i p ↦ if i = p.1 ∧ j = p.2 then 1 else 0

/-- Discard the second tensor factor. -/
noncomputable def discardSecond : FiniteKrausChannel J (I × J) I where
  kraus := discardSecondKraus I J
  completeness := by
    ext p q
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    by_cases hi : i = i'
    · subst i'
      by_cases hj : j = j'
      · subst j'
        simp [Matrix.sum_apply, discardSecondKraus, Matrix.mul_apply,
          ite_and, Finset.sum_ite_eq']
      · simp [Matrix.sum_apply, discardSecondKraus, Matrix.mul_apply, hj,
          Ne.symm hj, ite_and, Finset.sum_ite_eq']
    · simp [Matrix.sum_apply, discardSecondKraus, Matrix.mul_apply, hi,
        Ne.symm hi, ite_and, Finset.sum_ite_eq']

@[simp]
theorem discardSecond_kraus (j : J) :
    (discardSecond I J).kraus j = discardSecondKraus I J j := rfl

/-- The finite-Kraus discard channel acts as the usual partial trace over its
second factor. -/
theorem discardSecond_action
    (A : Matrix (I × J) (I × J) ℂ) :
    (discardSecond I J).action A = environmentPartialTrace I J A := by
  ext i i'
  simp only [action_apply, Matrix.sum_apply, discardSecond_kraus,
    discardSecondKraus,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    environmentPartialTrace_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [ite_and, Finset.sum_ite_eq]
  have hstar (p q : Prop) [Decidable p] [Decidable q] :
      (starRingEnd ℂ) (if p then if q then 1 else 0 else 0) =
        if p then if q then 1 else 0 else 0 := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  simp_rw [hstar]
  simp [Finset.sum_ite_eq]

/-- Kraus row that selects the first-factor basis value `i`. -/
def discardFirstKraus (i : I) : Matrix J (I × J) ℂ :=
  fun j p ↦ if i = p.1 ∧ j = p.2 then 1 else 0

/-- Discard the first tensor factor. -/
noncomputable def discardFirst : FiniteKrausChannel I (I × J) J where
  kraus := discardFirstKraus I J
  completeness := by
    ext p q
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    by_cases hi : i = i'
    · subst i'
      by_cases hj : j = j'
      · subst j'
        simp [Matrix.sum_apply, discardFirstKraus, Matrix.mul_apply,
          ite_and, Finset.sum_ite_eq']
      · simp [Matrix.sum_apply, discardFirstKraus, Matrix.mul_apply, hj,
          Ne.symm hj, ite_and, Finset.sum_ite_eq']
    · simp [Matrix.sum_apply, discardFirstKraus, Matrix.mul_apply, hi,
        Ne.symm hi, ite_and, Finset.sum_ite_eq']

@[simp]
theorem discardFirst_kraus (i : I) :
    (discardFirst I J).kraus i = discardFirstKraus I J i := rfl

/-- The finite-Kraus discard channel acts as the usual partial trace over its
first factor. -/
theorem discardFirst_action
    (A : Matrix (I × J) (I × J) ℂ) :
    (discardFirst I J).action A = firstFactorPartialTrace I J A := by
  ext j j'
  simp only [action_apply, Matrix.sum_apply, discardFirst_kraus,
    discardFirstKraus,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    firstFactorPartialTrace_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [ite_and, Finset.sum_ite_eq]
  have hstar (p q : Prop) [Decidable p] [Decidable q] :
      (starRingEnd ℂ) (if p then if q then 1 else 0 else 0) =
        if p then if q then 1 else 0 else 0 := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  simp_rw [hstar]
  simp [Finset.sum_ite_eq]

universe uK

/-- Dilating a finite Kraus channel and then discarding its explicit
environment reproduces the original channel action exactly. -/
theorem discardSecond_comp_dilationChannel_action
    {K : Type uK} [Fintype K] [DecidableEq K]
    (Phi : FiniteKrausChannel K I J) (A : Matrix I I ℂ) :
    ((discardSecond J K).comp Phi.dilationChannel).action A =
      Phi.action A := by
  rw [comp_action, discardSecond_action,
    environmentPartialTrace_dilationChannel]

end FiniteKrausChannel

end LinearRouting
