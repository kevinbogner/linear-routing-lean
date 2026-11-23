import LinearRouting.ExactPhaseBase
import LinearRouting.ExactPhaseTeleportation
import LinearRouting.Walsh

/-!
# Work operators for exact bit disclosure

The flip at address \(a\) and the phase for the complemented row
commute exactly on Bob's routing case. Their normalized sum is an
orthogonal matrix on Alice's case and has a known eigenvalue under
their product on Bob's case.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

private def workDelta (a : Address n) : Work n := Pi.single a 1

private def workFlipIndex (a : Address n) (w : Work n) : Work n :=
  w + workDelta a

private theorem workFlipIndex_involutive (a : Address n) :
    Function.Involutive (workFlipIndex a) := by
  intro w
  funext c
  change w c + workDelta a c + workDelta a c = w c
  rw [add_assoc, (by decide : ∀ z : ZMod 2, z + z = 0), add_zero]

private theorem workFlipIndex_ne (a : Address n) (w : Work n) :
    workFlipIndex a w ≠ w := by
  intro h
  have ha := congrFun h a
  change w a + workDelta a a = w a at ha
  rw [workDelta, Pi.single_eq_same] at ha
  exact (by decide : ∀ z : ZMod 2, z + 1 ≠ z) _ ha

/-- Flip the work bit at the selected address. -/
def workFlip (a : Address n) : Matrix (Work n) (Work n) ℂ :=
  fun w w' ↦ if w' = workFlipIndex a w then 1 else 0

private def workMask (row : Address n → Bool) (b : Address n) (c : Address n) :
    ZMod 2 :=
  if row (c + b) then 0 else 1

private def workPhaseValue (row : Address n → Bool) (b : Address n) (w : Work n) : ℂ :=
  (chi (∑ c, workMask row b c * w c) : ℂ)

/-- Apply \(Z\) at each address selected by the complemented row. -/
def workPhase (row : Address n → Bool) (b : Address n) :
    Matrix (Work n) (Work n) ℂ :=
  Matrix.diagonal (workPhaseValue row b)

private theorem workPhaseValue_mul_self (row : Address n → Bool) (b : Address n)
    (w : Work n) :
    workPhaseValue row b w * workPhaseValue row b w = 1 := by
  unfold workPhaseValue
  rw [← Complex.ofReal_mul, ← chi_add, (by decide : ∀ z : ZMod 2, z + z = 0)]
  simp

private theorem workPhaseValue_flip (row : Address n → Bool) (a b : Address n)
    (w : Work n) :
    workPhaseValue row b (workFlipIndex a w) =
      bitSign (!(row (a + b))) * workPhaseValue row b w := by
  have hsum : (∑ c, workMask row b c * (workFlipIndex a w) c) =
      (∑ c, workMask row b c * w c) + workMask row b a := by
    have hsplit : (∑ c, workMask row b c * (workFlipIndex a w) c) =
        (∑ c, workMask row b c * w c) +
          ∑ c, workMask row b c * workDelta a c := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [workFlipIndex, Pi.add_apply, mul_add]
    rw [hsplit]
    congr 1
    rw [Finset.sum_eq_single a
      (fun c _ hc => by rw [workDelta, Pi.single_eq_of_ne hc, mul_zero])
      (fun h => absurd (Finset.mem_univ a) h), workDelta, Pi.single_eq_same, mul_one]
  rw [workPhaseValue, hsum, chi_add, Complex.ofReal_mul, mul_comm]
  cases h : row (a + b) <;> simp [h, workMask, workPhaseValue]

theorem workFlip_transpose (a : Address n) : (workFlip a)ᵀ = workFlip a := by
  ext w w'
  have h : w = workFlipIndex a w' ↔ w' = workFlipIndex a w := by
    constructor <;> intro h
    · rw [h, workFlipIndex_involutive]
    · rw [h, workFlipIndex_involutive]
  simp [workFlip, h]

theorem workPhase_transpose (row : Address n → Bool) (b : Address n) :
    (workPhase row b)ᵀ = workPhase row b := by
  simp [workPhase]

theorem workFlip_conjTranspose (a : Address n) : (workFlip a)ᴴ = workFlip a := by
  conv_rhs => rw [← workFlip_transpose a]
  ext w w'
  by_cases h : w = workFlipIndex a w' <;> simp [workFlip, h]

theorem workPhase_conjTranspose (row : Address n → Bool) (b : Address n) :
    (workPhase row b)ᴴ = workPhase row b := by
  simp [workPhase, workPhaseValue]

private theorem workFlip_mul_apply (a : Address n) (M : Matrix (Work n) (Work n) ℂ)
    (w w' : Work n) :
    (workFlip a * M) w w' = M (workFlipIndex a w) w' := by
  simp [Matrix.mul_apply, workFlip, ite_mul, Finset.sum_ite_eq']

theorem workFlip_mul_self (a : Address n) : workFlip a * workFlip a = 1 := by
  ext w w'
  rw [workFlip_mul_apply]
  simp [workFlip, workFlipIndex_involutive a w, Matrix.one_apply, eq_comm]

theorem workPhase_mul_self (row : Address n → Bool) (b : Address n) :
    workPhase row b * workPhase row b = 1 := by
  rw [workPhase, Matrix.diagonal_mul_diagonal]
  simp [workPhaseValue_mul_self]

/-- The role selects the flip or the phase carrying the key sign. -/
def phaseWorkOperator (row : Address n → Bool) (z : Bool) (label : Label n) :
    Matrix (Work n) (Work n) ℂ :=
  if label.1 then bitSign z • workPhase row label.2 else workFlip label.2

theorem phaseWorkOperator_conjTranspose_mul (row : Address n → Bool)
    (z : Bool) (label : Label n) :
    (phaseWorkOperator row z label)ᴴ * phaseWorkOperator row z label = 1 := by
  rcases label with ⟨r, j⟩
  cases r <;> simp [phaseWorkOperator, workFlip_conjTranspose,
    workFlip_mul_self, workPhase_conjTranspose, workPhase_mul_self,
    smul_smul]

/-- The commutation sign is the sign of the complemented routing bit. -/
theorem work_comm (row : Address n → Bool) (a b : Address n) :
    workFlip a * workPhase row b =
      bitSign (!(row (a + b))) • (workPhase row b * workFlip a) := by
  ext w w'
  simp only [workPhase, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul, workFlip]
  by_cases h : w' = workFlipIndex a w
  · rw [if_pos h, one_mul, mul_one, h]
    exact workPhaseValue_flip row a b w
  · simp [h]

theorem work_trace_cross (row : Address n → Bool) (a b : Address n) :
    Matrix.trace (workFlip a * workPhase row b) = 0 := by
  simp [Matrix.trace, workPhase, Matrix.mul_diagonal, workFlip,
    fun w => Ne.symm (workFlipIndex_ne a w)]

/-- The work amplitude after including the Fourier phase in the sign. -/
def workMix (row : Address n → Bool) (a b : Address n) (z : Bool) :
    Matrix (Work n) (Work n) ℂ :=
  invSqrtTwo • (workFlip a + bitSign z • workPhase row b)

theorem workMix_apply (row : Address n → Bool) (a b : Address n) (z : Bool)
    (p p' : Work n) :
    workMix row a b z p p' =
      invSqrtTwo * (workFlip a p p' + bitSign z * workPhase row b p p') := rfl

theorem workMix_transpose (row : Address n → Bool) (a b : Address n) (z : Bool) :
    (workMix row a b z)ᵀ = workMix row a b z := by
  simp [workMix, workFlip_transpose, workPhase_transpose]

theorem workMix_conjTranspose (row : Address n → Bool) (a b : Address n) (z : Bool) :
    (workMix row a b z)ᴴ = workMix row a b z := by
  simp [workMix, workFlip_conjTranspose, workPhase_conjTranspose]

theorem workMix_false_mul_self (row : Address n → Bool) (a b : Address n)
    (z : Bool) (h : row (a + b) = false) :
    workMix row a b z * workMix row a b z = 1 := by
  have hc := work_comm row a b
  rw [h] at hc
  simp at hc
  unfold workMix
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, invSqrtTwo_mul_self]
  have hsq : (workFlip a + bitSign z • workPhase row b) *
      (workFlip a + bitSign z • workPhase row b) = (2 : ℂ) • 1 := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      bitSign_mul_self, one_smul, workFlip_mul_self, workPhase_mul_self, hc]
    rw [smul_neg, show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
    abel
  rw [hsq, smul_smul]
  norm_num

theorem workProduct_true_conjTranspose (row : Address n → Bool) (a b : Address n)
    (h : row (a + b) = true) :
    (workFlip a * workPhase row b)ᴴ = workFlip a * workPhase row b := by
  have hc := work_comm row a b
  rw [h] at hc
  simpa [Matrix.conjTranspose_mul, workFlip_conjTranspose, workPhase_conjTranspose]
    using hc.symm

theorem workProduct_true_mul_self (row : Address n → Bool) (a b : Address n)
    (h : row (a + b) = true) :
    (workFlip a * workPhase row b) * (workFlip a * workPhase row b) = 1 := by
  have hc : workFlip a * workPhase row b = workPhase row b * workFlip a := by
    simpa [h] using work_comm row a b
  calc
    (workFlip a * workPhase row b) * (workFlip a * workPhase row b)
        = workFlip a * (workPhase row b * workFlip a) * workPhase row b := by
          simp [mul_assoc]
    _ = (workFlip a * workFlip a) * (workPhase row b * workPhase row b) := by
      rw [← hc]
      simp [mul_assoc]
    _ = 1 := by simp [workFlip_mul_self, workPhase_mul_self]

theorem workMix_true_support (row : Address n → Bool) (a b : Address n)
    (z : Bool) (h : row (a + b) = true) :
    (workFlip a * workPhase row b) * workMix row a b z =
      bitSign z • workMix row a b z := by
  have hc : workFlip a * workPhase row b = workPhase row b * workFlip a := by
    simpa [h] using work_comm row a b
  have hu : (workFlip a * workPhase row b) * workFlip a = workPhase row b := by
    rw [hc, mul_assoc, workFlip_mul_self, mul_one]
  have hv : (workFlip a * workPhase row b) * workPhase row b = workFlip a := by
    rw [mul_assoc, workPhase_mul_self, mul_one]
  unfold workMix
  simp only [mul_smul_comm, mul_add, hu, hv, smul_smul]
  rw [mul_comm (bitSign z) invSqrtTwo, ← smul_smul]
  simp [smul_add, smul_smul, add_comm]

/-- Spectral projector for the sign of the known product of the work operators. -/
def workProjector (row : Address n → Bool) (a b : Address n) (key : Bool) :
    Matrix (Work n) (Work n) ℂ :=
  (2 : ℂ)⁻¹ • (1 + bitSign key • (workFlip a * workPhase row b))

theorem workProjector_sum (row : Address n → Bool) (a b : Address n) :
    ∑ key : Bool, workProjector row a b key = 1 := by
  rw [Fintype.sum_bool]
  simp only [workProjector, bitSign_true, bitSign_false]
  module

theorem workProjector_conjTranspose (row : Address n → Bool) (a b : Address n)
    (key : Bool) (h : row (a + b) = true) :
    (workProjector row a b key)ᴴ = workProjector row a b key := by
  simp [workProjector, workProduct_true_conjTranspose row a b h]

theorem workProjector_mul (row : Address n → Bool) (a b : Address n)
    (key key' : Bool) (h : row (a + b) = true) :
    workProjector row a b key * workProjector row a b key' =
      if key = key' then workProjector row a b key else 0 := by
  cases key <;> cases key' <;>
    simp only [workProjector, bitSign_false, bitSign_true,
      smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, workProduct_true_mul_self row a b h,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;> module

theorem workProjector_mul_workMix (row : Address n → Bool) (a b : Address n)
    (key z : Bool) (h : row (a + b) = true) :
    workProjector row a b key * workMix row a b z =
      if key = z then workMix row a b z else 0 := by
  unfold workProjector
  rw [smul_mul_assoc, add_mul, one_mul, smul_mul_assoc,
    workMix_true_support row a b z h]
  cases key <;> cases z <;>
    simp only [bitSign_false, bitSign_true, Bool.false_eq_true, Bool.true_eq_false,
      if_true, if_false] <;> module

end

end LinearRouting.ExactPhase
