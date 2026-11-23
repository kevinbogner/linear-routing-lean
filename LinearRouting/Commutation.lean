import LinearRouting.ExactPhaseWork

/-!
# Commutation of the work operators

The phase operator is the product of Pauli Z matrices selected by the
shifted row of the routing function. In the paper's two cases, the bit
flip at the chosen address anticommutes or commutes with that phase.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Pauli Z on the work qubit at address `c`. -/
def workPauliZ (c : Address n) : Matrix (Work n) (Work n) ℂ :=
  Matrix.diagonal fun w ↦ (chi (w c) : ℂ)

private theorem workPauliZ_commute (a b : Address n) :
    Commute (workPauliZ a) (workPauliZ b) := by
  show workPauliZ a * workPauliZ b = workPauliZ b * workPauliZ a
  simp only [workPauliZ, Matrix.diagonal_mul_diagonal]
  simp_rw [mul_comm]

private theorem chi_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ZMod 2) :
    (chi (∑ i ∈ s, v i) : ℂ) = ∏ i ∈ s, (chi (v i) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
      simp [Finset.sum_insert hi, Finset.prod_insert hi, chi_add, ← hs]

/-- Identify the phase operator in the circuit with the product in the paper. -/
theorem workPhase_eq_pauliZ_product (row : Address n → Bool) (b : Address n) :
    workPhase row b =
      (Finset.univ.filter (fun c ↦ row (b + c) = false)).noncommProd
        workPauliZ (fun a _ c _ _ ↦ workPauliZ_commute a c) := by
  let selected := Finset.univ.filter (fun c ↦ row (b + c) = false)
  let sign (c : Address n) (w : Work n) : ℂ := (chi (w c) : ℂ)
  change Matrix.diagonal
      (fun w : Work n ↦ (chi (∑ c, (if row (c + b) then 0 else 1) * w c) : ℂ)) =
    selected.noncommProd workPauliZ _
  calc
    _ = Matrix.diagonal (∏ c ∈ selected, sign c) := by
      apply congrArg Matrix.diagonal
      funext w
      simp only [Finset.prod_apply, sign]
      rw [← chi_sum, Finset.sum_filter]
      apply congrArg (fun p : ZMod 2 ↦ (chi p : ℂ))
      exact Finset.sum_congr rfl fun c _ ↦ by cases h : row (b + c) <;> simp [add_comm c b, h]
    _ = _ := by
      change (Matrix.diagonalRingHom (Work n) ℂ) (∏ c ∈ selected, sign c) =
        selected.noncommProd workPauliZ _
      rw [← Finset.noncommProd_eq_prod selected sign, Finset.map_noncommProd]
      rfl

/-- Commutation lemma. The chosen addresses differ by Bob's input. -/
theorem commutation (f : Address n → Address n → Bool) (x y a : Address n) :
    workFlip a * workPhase (f x) (a + y) =
      if f x y = false then -(workPhase (f x) (a + y) * workFlip a)
      else workPhase (f x) (a + y) * workFlip a := by
  have hcancel : a + (a + y) = y := by
    funext i
    change a i + (a i + y i) = y i
    rw [← add_assoc, (by decide : ∀ z : ZMod 2, z + z = 0), zero_add]
  rw [work_comm, hcancel]
  cases f x y <;> simp

end

end LinearRouting.ExactPhase
