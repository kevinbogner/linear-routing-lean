import LinearRouting.FiniteKraus

/-!
# Tensor products of finite Kraus channels

The routing proof applies one local channel on each half of a Schmidt-form
resource.  This file constructs their tensor-product Kraus channel and proves
its action on simple Kronecker tensors.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators Kronecker

namespace FiniteKrausChannel

universe uK uL uI uJ uO uP

variable {K : Type uK} [Fintype K]
variable {L : Type uL} [Fintype L]
variable {I : Type uI} {J : Type uJ} {O : Type uO} {P : Type uP}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]

private theorem tensor_completeness
    (Phi : FiniteKrausChannel K I O)
    (Psi : FiniteKrausChannel L J P) :
    ∑ q : K × L,
        (Phi.kraus q.1 ⊗ₖ Psi.kraus q.2)ᴴ *
          (Phi.kraus q.1 ⊗ₖ Psi.kraus q.2) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ k, ∑ l,
        (Phi.kraus k ⊗ₖ Psi.kraus l)ᴴ *
          (Phi.kraus k ⊗ₖ Psi.kraus l)) =
        ∑ k, ∑ l,
          ((Phi.kraus k)ᴴ * Phi.kraus k) ⊗ₖ
            ((Psi.kraus l)ᴴ * Psi.kraus l) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro l _hl
      rw [conjTranspose_kronecker, Matrix.mul_kronecker_mul]
    _ = (∑ k, (Phi.kraus k)ᴴ * Phi.kraus k) ⊗ₖ
          (∑ l, (Psi.kraus l)ᴴ * Psi.kraus l) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      simp only [Matrix.kronecker_apply, Matrix.sum_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ = 1 := by
      rw [Phi.completeness, Psi.completeness, Matrix.one_kronecker_one]

/-- Tensor product of two finite Kraus channels. -/
noncomputable def tensor
    (Phi : FiniteKrausChannel K I O)
    (Psi : FiniteKrausChannel L J P) :
    FiniteKrausChannel (K × L) (I × J) (O × P) where
  kraus q := Phi.kraus q.1 ⊗ₖ Psi.kraus q.2
  completeness := tensor_completeness Phi Psi

@[simp]
theorem tensor_kraus
    (Phi : FiniteKrausChannel K I O)
    (Psi : FiniteKrausChannel L J P) (q : K × L) :
    (Phi.tensor Psi).kraus q = Phi.kraus q.1 ⊗ₖ Psi.kraus q.2 := rfl

/-- A product channel maps a simple tensor to the tensor product of the two
local outputs. -/
theorem tensor_action_kronecker
    (Phi : FiniteKrausChannel K I O)
    (Psi : FiniteKrausChannel L J P)
    (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    (Phi.tensor Psi).action (X ⊗ₖ Y) =
      Phi.action X ⊗ₖ Psi.action Y := by
  classical
  rw [action_apply, action_apply, action_apply, Fintype.sum_prod_type]
  calc
    (∑ k, ∑ l,
        (Phi.kraus k ⊗ₖ Psi.kraus l) * (X ⊗ₖ Y) *
          (Phi.kraus k ⊗ₖ Psi.kraus l)ᴴ) =
        ∑ k, ∑ l,
          (Phi.kraus k * X * (Phi.kraus k)ᴴ) ⊗ₖ
            (Psi.kraus l * Y * (Psi.kraus l)ᴴ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro l _hl
      rw [conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul]
    _ = (∑ k, Phi.kraus k * X * (Phi.kraus k)ᴴ) ⊗ₖ
          (∑ l, Psi.kraus l * Y * (Psi.kraus l)ᴴ) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      simp only [Matrix.kronecker_apply, Matrix.sum_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]

end FiniteKrausChannel

end LinearRouting
