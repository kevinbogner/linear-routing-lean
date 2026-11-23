import LinearRouting.FiniteKrausTensor
import LinearRouting.FiniteKrausReindex
import LinearRouting.FiniteKrausPartialTrace

/-!
# Recording a classical outcome

An outcome in the output basis selects a Kraus operator. A fixed input
label can also be written into a separate register in that same operation.
-/

namespace LinearRouting.FiniteKrausChannel

open Matrix
open scoped Kronecker

variable {I O F T : Type*}
variable [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]

/-- Keep the rows corresponding to one measurement outcome and append a
fixed computational-basis label. -/
def recordedKraus (V : Matrix O I ℂ) (flag : O → F) (tag : T) (k : F) :
    Matrix (O × T) I ℂ :=
  fun p i ↦ if p.2 = tag ∧ flag p.1 = k then V p.1 i else 0

/-- Apply an isometry, measure the indicated output label, and record a
fixed tag. The Kraus index retains the measurement result in the environment. -/
noncomputable def recorded (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (flag : O → F) (tag : T) : FiniteKrausChannel F I (O × T) where
  kraus := recordedKraus V flag tag
  completeness := by
    ext i j
    rw [← hV]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, recordedKraus]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o _
    simp [ite_and, apply_ite (starRingEnd ℂ), ite_mul]

@[simp]
theorem recorded_kraus (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (flag : O → F) (tag : T) (k : F) :
    (recorded V hV flag tag).kraus k = recordedKraus V flag tag k := rfl

omit [Fintype F] [Fintype T] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem recordedKraus_mul (V : Matrix O I ℂ) (flag : O → F) (tag : T)
    (k : F) {J : Type*} (W : Matrix I J ℂ) :
    recordedKraus V flag tag k * W = recordedKraus (V * W) flag tag k := by
  ext p j
  by_cases h : p.2 = tag ∧ flag p.1 = k <;> simp [recordedKraus, Matrix.mul_apply, h]

/-- Different measurement outcomes have zero off-diagonal blocks. -/
theorem recorded_action_apply (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (flag : O → F) (tag : T) (Q : Matrix I I ℂ) (p p' : O × T) :
    (recorded V hV flag tag).action Q p p' =
      if p.2 = tag ∧ p'.2 = tag ∧ flag p.1 = flag p'.1 then
        (V * Q * Vᴴ) p.1 p'.1 else 0 := by
  simp only [action_apply, Matrix.sum_apply, recorded_kraus, recordedKraus_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, recordedKraus]
  by_cases hp : p.2 = tag <;> by_cases hp' : p'.2 = tag <;>
    simp [hp, hp', mul_ite, apply_ite (starRingEnd ℂ), Finset.sum_ite_irrel]
  by_cases h : flag p.1 = flag p'.1
  · simp [h]
  · simp [h, Ne.symm h]

omit [DecidableEq I] [DecidableEq O] [Fintype F] [Fintype T] in
private theorem equivalenceIsometry_mul_apply {P J : Type*} [DecidableEq P]
    (e : O ≃ P) (V : Matrix O J ℂ) (p : P) (j : J) :
    (equivalenceIsometry e * V) p j = V (e.symm p) j := by
  simp only [Matrix.mul_apply, equivalenceIsometry, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm p)]
  · simp
  · intro o _ ho
    exact if_neg (fun h ↦ ho (e.eq_symm_apply.mpr h.symm))
  · simp

/-- Left multiplication by a reindexing channel just relabels each Kraus row. -/
theorem reindex_comp_kraus_apply {K P : Type*} [Fintype K] [Fintype P] [DecidableEq P]
    (e : O ≃ P) (Φ : FiniteKrausChannel K I O) (k : K × Fin 1) (p : P) (i : I) :
    ((reindex e).comp Φ).kraus k p i = Φ.kraus k.1 (e.symm p) i :=
  equivalenceIsometry_mul_apply e (Φ.kraus k.1) p i

/-- Kraus families with the same matrices up to reindexing have the same
channel action. -/
theorem action_eq_of_kraus_equiv {K L : Type*} [Fintype K] [Fintype L]
    (Φ : FiniteKrausChannel K I O) (Ψ : FiniteKrausChannel L I O)
    (e : K ≃ L) (h : ∀ k, Φ.kraus k = Ψ.kraus (e k)) (Q : Matrix I I ℂ) :
    Φ.action Q = Ψ.action Q := by
  simp only [action_apply, h]
  exact Equiv.sum_comp e (fun k ↦ Ψ.kraus k * Q * (Ψ.kraus k)ᴴ)

private def tagBlock (Q : Matrix (I × T) (I × T) ℂ) (tag : T) : Matrix I I ℂ :=
  Q.submatrix (fun i ↦ (i, tag)) (fun i ↦ (i, tag))

/-- Read a classical tag, apply the channel it selects, and discard the tag. -/
noncomputable def readTag {K : Type*} [Fintype K]
    (decode : T → FiniteKrausChannel K I O) : FiniteKrausChannel (T × K) (I × T) O where
  kraus p := (decode p.1).kraus p.2 * discardSecondKraus I T p.1
  completeness := by
    rw [Fintype.sum_prod_type]
    change (∑ t, ∑ k, ((decode t).kraus k * discardSecondKraus I T t)ᴴ *
      ((decode t).kraus k * discardSecondKraus I T t)) = 1
    rw [← (discardSecond I T).completeness]
    apply Finset.sum_congr rfl
    intro tag _
    let S := discardSecondKraus I T tag
    calc
      _ = ∑ k, Sᴴ * (((decode tag).kraus k)ᴴ * (decode tag).kraus k) * S := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [S, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, (decode tag).completeness, Matrix.mul_one]
        rfl

private theorem select_tag (Q : Matrix (I × T) (I × T) ℂ) (tag : T) :
    discardSecondKraus I T tag * Q * (discardSecondKraus I T tag)ᴴ = tagBlock Q tag := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    discardSecondKraus, tagBlock, ite_and, ite_mul, mul_ite, apply_ite (starRingEnd ℂ)]

theorem readTag_action {K : Type*} [Fintype K] (decode : T → FiniteKrausChannel K I O)
    (Q : Matrix (I × T) (I × T) ℂ) :
    (readTag decode).action Q = ∑ t, (decode t).action (tagBlock Q t) := by
  simp only [action_apply, Fintype.sum_prod_type, readTag]
  apply Finset.sum_congr rfl
  intro tag _
  apply Finset.sum_congr rfl
  intro k _
  rw [← select_tag, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- When the input tag has a fixed value, reading it selects one channel. -/
theorem readTag_action_fixed {K : Type*} [Fintype K] (decode : T → FiniteKrausChannel K I O)
    (Q : Matrix (I × T) (I × T) ℂ) (tag : T) (M : Matrix I I ℂ)
    (hQ : ∀ i j t, Q (i, t) (j, t) = if t = tag then M i j else 0) :
    (readTag decode).action Q = (decode tag).action M := by
  rw [readTag_action, Finset.sum_eq_single tag]
  · congr 1
    ext i j
    simpa [tagBlock] using hQ i j tag
  · intro t _ ht
    have htQ : tagBlock Q t = 0 := by
      ext i j
      simpa [tagBlock, ht] using hQ i j t
    rw [htQ, map_zero]
  · simp

end LinearRouting.FiniteKrausChannel
