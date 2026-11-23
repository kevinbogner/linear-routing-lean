import LinearRouting.FiniteKrausDilation

/-!
# Spectral purification of finite-dimensional density matrices

An `n`-dimensional density matrix is purified on the product basis
`Fin n × Fin n`.  The construction uses its nonnegative spectral weights
and eigenvector unitary.  The resulting rank-one matrix is positive,
normalized, and has the original density matrix as its first marginal.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

variable {n : ℕ}

/-- Spectral weights used by the canonical finite purification. -/
noncomputable def purificationWeights (rho : DensityMatrix n) : Fin n → ℝ :=
  rho.posSemidef.1.eigenvalues

/-- Eigenvector unitary used by the canonical finite purification. -/
noncomputable def purificationEigenvectorUnitary (rho : DensityMatrix n) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  rho.posSemidef.1.eigenvectorUnitary

theorem purificationWeights_nonneg (rho : DensityMatrix n) (i : Fin n) :
    0 ≤ purificationWeights rho i :=
  rho.posSemidef.eigenvalues_nonneg i

theorem sum_purificationWeights (rho : DensityMatrix n) :
    ∑ i, purificationWeights rho i = 1 := by
  have hsum :
      (∑ i, (rho.posSemidef.1.eigenvalues i : ℂ)) = 1 :=
    rho.posSemidef.1.trace_eq_sum_eigenvalues.symm.trans rho.trace_eq_one
  simpa [purificationWeights] using congrArg Complex.re hsum

/-- The Schmidt coefficient associated with a spectral weight. -/
noncomputable def purificationSchmidtCoefficient
    (rho : DensityMatrix n) (i : Fin n) : ℝ :=
  Real.sqrt (purificationWeights rho i)

theorem purificationSchmidtCoefficient_nonneg
    (rho : DensityMatrix n) (i : Fin n) :
    0 ≤ purificationSchmidtCoefficient rho i :=
  Real.sqrt_nonneg _

theorem purificationSchmidtCoefficient_sq
    (rho : DensityMatrix n) (i : Fin n) :
    (purificationSchmidtCoefficient rho i) ^ 2 =
      purificationWeights rho i := by
  rw [pow_two, purificationSchmidtCoefficient]
  exact Real.mul_self_sqrt (purificationWeights_nonneg rho i)

/-- The spectral weights and eigenvector unitary reconstruct the density
matrix exactly. -/
theorem purification_spectral_decomposition (rho : DensityMatrix n) :
    rho.val =
      (purificationEigenvectorUnitary rho : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i ↦ (purificationWeights rho i : ℂ)) *
        star (purificationEigenvectorUnitary rho :
          Matrix (Fin n) (Fin n) ℂ) := by
  unfold purificationEigenvectorUnitary purificationWeights
  have hweights :
      (fun i ↦ (rho.posSemidef.1.eigenvalues i : ℂ)) =
        Complex.ofReal ∘ rho.posSemidef.1.eigenvalues := by
    rfl
  rw [hweights]
  exact rho.posSemidef.1.spectral_theorem

/-- The canonical purification vector
`sum_r sqrt(lambda_r) (U|r⟩) tensor |r⟩`. -/
noncomputable def purificationVector (rho : DensityMatrix n) :
    Fin n × Fin n → ℂ :=
  fun p ↦
    (purificationEigenvectorUnitary rho : Matrix (Fin n) (Fin n) ℂ)
        p.1 p.2 *
      (purificationSchmidtCoefficient rho p.2 : ℂ)

/-- Rank-one density operator of the canonical purification vector. -/
noncomputable def purificationPureMatrix (rho : DensityMatrix n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.vecMulVec (purificationVector rho) (star (purificationVector rho))

theorem purificationPureMatrix_posSemidef (rho : DensityMatrix n) :
    (purificationPureMatrix rho).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star (purificationVector rho)

/-- A finite partial trace preserves the ordinary matrix trace. -/
theorem trace_environmentPartialTrace
    {J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix (J × K) (J × K) ℂ) :
    (environmentPartialTrace J K A).trace = A.trace := by
  rw [Matrix.trace, Matrix.trace, Fintype.sum_prod_type]
  rfl

/-- The retained marginal of the canonical purification is the original
density matrix. -/
theorem environmentPartialTrace_purificationPureMatrix
    (rho : DensityMatrix n) :
    environmentPartialTrace (Fin n) (Fin n) (purificationPureMatrix rho) =
      rho.val := by
  rw [rho.posSemidef.1.spectral_theorem]
  ext i i'
  simp only [environmentPartialTrace_apply, purificationPureMatrix,
    Matrix.vecMulVec_apply, Pi.star_apply, purificationVector,
    purificationSchmidtCoefficient, purificationEigenvectorUnitary,
    purificationWeights,
    Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq', Matrix.star_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  have hsqrt :
      (Real.sqrt (rho.posSemidef.1.eigenvalues r) : ℂ) *
          (Real.sqrt (rho.posSemidef.1.eigenvalues r) : ℂ) =
        (rho.posSemidef.1.eigenvalues r : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (rho.posSemidef.eigenvalues_nonneg r)
  simp only [star_mul, Function.comp_apply]
  rw [← starRingEnd_apply, Complex.conj_ofReal]
  ring_nf
  rw [pow_two, hsqrt]
  ac_rfl

/-- The purification matrix has trace one. -/
theorem trace_purificationPureMatrix (rho : DensityMatrix n) :
    (purificationPureMatrix rho).trace = 1 := by
  have hmarg := congrArg Matrix.trace
    (environmentPartialTrace_purificationPureMatrix rho)
  rw [trace_environmentPartialTrace, rho.trace_eq_one] at hmarg
  exact hmarg

/-- The canonical purification vector is normalized. -/
theorem purificationVector_normalized (rho : DensityMatrix n) :
    star (purificationVector rho) ⬝ᵥ purificationVector rho = 1 := by
  rw [dotProduct_comm]
  rw [← Matrix.trace_vecMulVec]
  exact trace_purificationPureMatrix rho

/-- Reindex the product-basis purification as the repository's standard
`DensityMatrix (n*n)` bundle. -/
noncomputable def purificationDensity (rho : DensityMatrix n) :
    DensityMatrix (n * n) where
  val := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (purificationPureMatrix rho)
  posSemidef := by
    rw [Matrix.reindex_apply]
    exact (purificationPureMatrix_posSemidef rho).submatrix
      finProdFinEquiv.symm
  trace_eq_one := by
    calc
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
          (purificationPureMatrix rho)).trace =
          (purificationPureMatrix rho).trace := by
        rw [Matrix.reindex_apply, Matrix.trace, Matrix.trace]
        exact Equiv.sum_comp finProdFinEquiv.symm
          (fun p ↦ purificationPureMatrix rho p p)
      _ = 1 := trace_purificationPureMatrix rho

@[simp]
theorem purificationDensity_val (rho : DensityMatrix n) :
    (purificationDensity rho).val =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (purificationPureMatrix rho) := rfl

end LinearRouting
