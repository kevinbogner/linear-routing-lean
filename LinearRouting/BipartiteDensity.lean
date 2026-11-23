import LinearRouting.DensityPurification
import LinearRouting.ProductDensityMatrix

/-!
# Product indexing and marginals for bipartite states
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

/-- Move a standard `Fin (l*r)` matrix back to the explicit product basis. -/
noncomputable def productMatrixOfReindexed {l r : ℕ}
    (A : Matrix (Fin (l * r)) (Fin (l * r)) ℂ) :
    Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ :=
  Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm A

@[simp]
theorem reindexProductMatrix_productMatrixOfReindexed {l r : ℕ}
    (A : Matrix (Fin (l * r)) (Fin (l * r)) ℂ) :
    reindexProductMatrix (productMatrixOfReindexed A) = A := by
  ext i j
  change A (finProdFinEquiv (finProdFinEquiv.symm i))
      (finProdFinEquiv (finProdFinEquiv.symm j)) = A i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp]
theorem productMatrixOfReindexed_reindexProductMatrix {l r : ℕ}
    (A : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ) :
    productMatrixOfReindexed (reindexProductMatrix A) = A := by
  ext i j
  change A (finProdFinEquiv.symm (finProdFinEquiv i))
      (finProdFinEquiv.symm (finProdFinEquiv j)) = A i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem trace_productMatrixOfReindexed {l r : ℕ}
    (A : Matrix (Fin (l * r)) (Fin (l * r)) ℂ) :
    (productMatrixOfReindexed A).trace = A.trace := by
  rw [productMatrixOfReindexed, Matrix.reindex_apply,
    Matrix.trace, Matrix.trace]
  exact Equiv.sum_comp finProdFinEquiv (fun i ↦ A i i)

theorem posSemidef_productMatrixOfReindexed {l r : ℕ}
    {A : Matrix (Fin (l * r)) (Fin (l * r)) ℂ}
    (hA : A.PosSemidef) : (productMatrixOfReindexed A).PosSemidef := by
  unfold productMatrixOfReindexed
  rw [Matrix.reindex_apply]
  exact hA.submatrix finProdFinEquiv

/-- Partial trace over the first factor, retaining the second. -/
def firstFactorPartialTrace (I J : Type*) [Fintype I] :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun A j j' := ∑ i, A (i, j) (i, j')
  map_add' A B := by
    ext j j'
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c A := by
    ext j j'
    simp [Finset.mul_sum]

@[simp]
theorem firstFactorPartialTrace_apply
    {I J : Type*} [Fintype I]
    (A : Matrix (I × J) (I × J) ℂ) (j j' : J) :
    firstFactorPartialTrace I J A j j' = ∑ i, A (i, j) (i, j') := rfl

theorem environmentPartialTrace_posSemidef
    {I J : Type*} [Fintype I] [Fintype J]
    {A : Matrix (I × J) (I × J) ℂ} (hA : A.PosSemidef) :
    (environmentPartialTrace I J A).PosSemidef := by
  have heq : environmentPartialTrace I J A =
      ∑ j : J, A.submatrix (fun i ↦ (i, j)) (fun i ↦ (i, j)) := by
    ext i i'
    simp only [environmentPartialTrace_apply, Matrix.sum_apply,
      Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum Finset.univ fun j _ ↦
    hA.submatrix (fun i ↦ (i, j))

theorem firstFactorPartialTrace_posSemidef
    {I J : Type*} [Fintype I] [Fintype J]
    {A : Matrix (I × J) (I × J) ℂ} (hA : A.PosSemidef) :
    (firstFactorPartialTrace I J A).PosSemidef := by
  have heq : firstFactorPartialTrace I J A =
      ∑ i : I, A.submatrix (fun j ↦ (i, j)) (fun j ↦ (i, j)) := by
    ext j j'
    simp only [firstFactorPartialTrace_apply, Matrix.sum_apply,
      Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum Finset.univ fun i _ ↦
    hA.submatrix (fun j ↦ (i, j))

theorem trace_firstFactorPartialTrace
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (I × J) (I × J) ℂ) :
    (firstFactorPartialTrace I J A).trace = A.trace := by
  rw [Matrix.trace, Matrix.trace, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- Left marginal of a density matrix presented on `Fin (l*r)`. -/
noncomputable def bipartiteLeftMarginal {l r : ℕ}
    (rho : DensityMatrix (l * r)) : DensityMatrix l where
  val := environmentPartialTrace (Fin l) (Fin r)
    (productMatrixOfReindexed rho.val)
  posSemidef := environmentPartialTrace_posSemidef
    (posSemidef_productMatrixOfReindexed rho.posSemidef)
  trace_eq_one := by
    rw [trace_environmentPartialTrace, trace_productMatrixOfReindexed,
      rho.trace_eq_one]

/-- Right marginal of a density matrix presented on `Fin (l*r)`. -/
noncomputable def bipartiteRightMarginal {l r : ℕ}
    (rho : DensityMatrix (l * r)) : DensityMatrix r where
  val := firstFactorPartialTrace (Fin l) (Fin r)
    (productMatrixOfReindexed rho.val)
  posSemidef := firstFactorPartialTrace_posSemidef
    (posSemidef_productMatrixOfReindexed rho.posSemidef)
  trace_eq_one := by
    rw [trace_firstFactorPartialTrace, trace_productMatrixOfReindexed,
      rho.trace_eq_one]

/-- The smaller rank of the two marginals. For a pure shared state this is the
Schmidt rank. -/
noncomputable def sharedResourceDimension {l r : ℕ}
    (rho : DensityMatrix (l * r)) : ℕ :=
  min (bipartiteLeftMarginal rho).val.rank
    (bipartiteRightMarginal rho).val.rank

/-- Qubit cost corresponding to `sharedResourceDimension`. -/
noncomputable def sharedResourceCost {l r : ℕ}
    (rho : DensityMatrix (l * r)) : ℝ :=
  Real.logb 2 (sharedResourceDimension rho : ℝ)

end LinearRouting
