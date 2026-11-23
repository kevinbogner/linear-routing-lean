import LinearRouting.FiniteKraus

/-!
# Finite Kraus dilations

This file gives the concrete finite-dimensional dilation of a finite Kraus
channel.  Its Kraus matrices are stacked into one isometry with output basis
`J × K`; tracing out the explicit finite environment `K` recovers the
original channel action.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

universe uK uI uJ

/-- Partial trace over a finite environment `K`, with the retained system in
the first component of `J × K`. -/
def environmentPartialTrace
    (J : Type uJ) (K : Type uK)
    [Fintype K] :
    Matrix (J × K) (J × K) ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun A j j' := ∑ k, A (j, k) (j', k)
  map_add' A B := by
    ext j j'
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c A := by
    ext j j'
    simp [Finset.mul_sum]

@[simp]
theorem environmentPartialTrace_apply
    {J : Type uJ} {K : Type uK} [Fintype K]
    (A : Matrix (J × K) (J × K) ℂ) (j j' : J) :
    environmentPartialTrace J K A j j' = ∑ k, A (j, k) (j', k) := rfl

namespace FiniteKrausChannel

variable {K : Type uK} [Fintype K]
variable {I : Type uI} {J : Type uJ}
variable [Fintype I] [DecidableEq I]
variable [Fintype J] [DecidableEq J]

/-- Stack the Kraus matrices into one matrix from `I` to the enlarged output
basis `J × K`. -/
def stackedIsometry (Phi : FiniteKrausChannel K I J) :
    Matrix (J × K) I ℂ :=
  fun jk i ↦ Phi.kraus jk.2 jk.1 i

@[simp]
theorem stackedIsometry_apply (Phi : FiniteKrausChannel K I J)
    (j : J) (k : K) (i : I) :
    Phi.stackedIsometry (j, k) i = Phi.kraus k j i := rfl

/-- The trace-preserving Kraus completeness relation says exactly that the
stacked dilation matrix is an isometry. -/
theorem stackedIsometry_conjTranspose_mul
    (Phi : FiniteKrausChannel K I J) :
    Phi.stackedIsometryᴴ * Phi.stackedIsometry = 1 := by
  ext i i'
  have hcomplete := congrFun (congrFun Phi.completeness i) i'
  simp only [Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hcomplete ⊢
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact hcomplete

section DilationChannel

variable [DecidableEq K]

/-- The one-Kraus channel implemented by the stacked isometry. -/
noncomputable def dilationChannel (Phi : FiniteKrausChannel K I J) :
    FiniteKrausChannel (Fin 1) I (J × K) :=
  ofIsometry Phi.stackedIsometry Phi.stackedIsometry_conjTranspose_mul

@[simp]
theorem dilationChannel_action (Phi : FiniteKrausChannel K I J)
    (X : Matrix I I ℂ) :
    Phi.dilationChannel.action X =
      Phi.stackedIsometry * X * Phi.stackedIsometryᴴ := by
  exact ofIsometry_action _ _ _

end DilationChannel

/-- Tracing out the explicit Kraus environment of the dilated output
recovers the original channel action. -/
theorem environmentPartialTrace_stackedIsometry
    (Phi : FiniteKrausChannel K I J) (X : Matrix I I ℂ) :
    environmentPartialTrace J K
        (Phi.stackedIsometry * X * Phi.stackedIsometryᴴ) =
      Phi.action X := by
  ext j j'
  simp [environmentPartialTrace, stackedIsometry, action_apply,
    Matrix.sum_apply, Matrix.mul_apply]

/-- Channel-level form of the finite dilation identity. -/
theorem environmentPartialTrace_dilationChannel
    [DecidableEq K] (Phi : FiniteKrausChannel K I J) (X : Matrix I I ℂ) :
    environmentPartialTrace J K (Phi.dilationChannel.action X) =
      Phi.action X := by
  rw [dilationChannel_action,
    environmentPartialTrace_stackedIsometry]

end FiniteKrausChannel

end LinearRouting
