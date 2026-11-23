import Mathlib

/-!
# Finite-dimensional density matrices

A density matrix is positive semidefinite with trace one. The full trace
distance is the sum of the absolute eigenvalues of the difference.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

variable {n : ℕ}

/-- A finite-dimensional density matrix. -/
structure DensityMatrix (n : ℕ) where
  val : Matrix (Fin n) (Fin n) ℂ
  posSemidef : val.PosSemidef
  trace_eq_one : val.trace = 1

instance : Coe (DensityMatrix n) (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨DensityMatrix.val⟩

@[simp] theorem DensityMatrix.coe_val (ρ : DensityMatrix n) :
    ((ρ : Matrix (Fin n) (Fin n) ℂ)) = ρ.val := rfl

/-- Spectral trace norm of a Hermitian matrix. -/
noncomputable def hermitianTraceNorm (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

theorem hermitianTraceNorm_nonneg (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    0 ≤ hermitianTraceNorm A hA := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Hermitian difference of two density matrices. -/
theorem density_sub_isHermitian (ρ σ : DensityMatrix n) :
    (ρ.val - σ.val).IsHermitian :=
  ρ.posSemidef.1.sub σ.posSemidef.1

/-- Full, unhalved trace distance used by the paper. -/
noncomputable def densityTraceDistance (ρ σ : DensityMatrix n) : ℝ :=
  hermitianTraceNorm (ρ.val - σ.val) (density_sub_isHermitian ρ σ)

theorem densityTraceDistance_nonneg (ρ σ : DensityMatrix n) :
    0 ≤ densityTraceDistance ρ σ :=
  hermitianTraceNorm_nonneg _ _

@[simp] theorem densityTraceDistance_self (rho : DensityMatrix n) :
    densityTraceDistance rho rho = 0 := by
  unfold densityTraceDistance hermitianTraceNorm
  have h := (density_sub_isHermitian rho rho).eigenvalues_eq_zero_iff.mpr
    (sub_self rho.val)
  rw [h]
  simp

end LinearRouting
