import LinearRouting.DensityMatrix

/-!
# Reindexing density matrices between product and finite carriers
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

/-- Reindex a matrix on `Fin n × Fin m` as a matrix on `Fin (n*m)`. -/
noncomputable def reindexProductMatrix {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin (n * m)) (Fin (n * m)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv A

theorem trace_reindexProductMatrix {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (reindexProductMatrix A).trace = A.trace := by
  rw [reindexProductMatrix, Matrix.reindex_apply, Matrix.trace, Matrix.trace]
  exact Equiv.sum_comp finProdFinEquiv.symm (fun p ↦ A p p)

theorem posSemidef_reindexProductMatrix {n m : ℕ}
    {A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ}
    (hA : A.PosSemidef) : (reindexProductMatrix A).PosSemidef := by
  unfold reindexProductMatrix
  rw [Matrix.reindex_apply]
  exact hA.submatrix finProdFinEquiv.symm

/-- Bundle a positive trace-one product-indexed matrix as a density matrix. -/
noncomputable def densityOfProductMatrix {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (hA : A.PosSemidef) (htrace : A.trace = 1) : DensityMatrix (n * m) where
  val := reindexProductMatrix A
  posSemidef := posSemidef_reindexProductMatrix hA
  trace_eq_one := (trace_reindexProductMatrix A).trans htrace

end LinearRouting
