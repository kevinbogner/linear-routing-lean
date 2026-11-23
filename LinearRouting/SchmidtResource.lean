import LinearRouting.BipartiteDensity

/-!
# Schmidt-form source states

The two marginals of a normalized pure source are diagonal in the supplied
Schmidt basis, with the supplied weights on the diagonal.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

/-- Schmidt-form vector on the product basis. -/
noncomputable def schmidtVector {d : ℕ} (lam : Fin d → ℝ) :
    Fin d × Fin d → ℂ :=
  fun p ↦ if p.1 = p.2 then (Real.sqrt (lam p.1) : ℂ) else 0

/-- Rank-one density operator of the Schmidt-form vector. -/
noncomputable def schmidtPureMatrix {d : ℕ} (lam : Fin d → ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (schmidtVector lam) (star (schmidtVector lam))

theorem schmidtPureMatrix_posSemidef {d : ℕ} (lam : Fin d → ℝ) :
    (schmidtPureMatrix lam).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (schmidtVector lam)

theorem trace_schmidtPureMatrix {d : ℕ} (lam : Fin d → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) :
    (schmidtPureMatrix lam).trace = ∑ r, (lam r : ℂ) := by
  rw [schmidtPureMatrix, Matrix.trace_vecMulVec, dotProduct,
    Fintype.sum_prod_type]
  simp only [schmidtVector]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.sum_eq_single r]
  · simp only [Pi.star_apply, schmidtVector, if_pos]
    rw [← starRingEnd_apply, Complex.conj_ofReal]
    norm_cast
    exact Real.mul_self_sqrt (hlam r)
  · intro s _hs hsr
    simp [Ne.symm hsr]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem environmentPartialTrace_schmidtPureMatrix_of_nonneg
    {d : ℕ} (lam : Fin d → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    environmentPartialTrace (Fin d) (Fin d) (schmidtPureMatrix lam) =
      Matrix.diagonal (fun a ↦ (lam a : ℂ)) := by
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun a ↦ (Real.sqrt (lam a) : ℂ)
  calc
    environmentPartialTrace (Fin d) (Fin d) (schmidtPureMatrix lam) =
        D * Dᴴ := by
      ext a b
      simp only [environmentPartialTrace_apply, schmidtPureMatrix,
        Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply]
      rfl
    _ = Matrix.diagonal (fun a ↦ (lam a : ℂ)) := by
      simp only [D]
      rw [Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      simp only [Pi.star_apply]
      rw [← starRingEnd_apply, Complex.conj_ofReal]
      norm_cast
      exact Real.mul_self_sqrt (hlam a)

theorem firstFactorPartialTrace_schmidtPureMatrix_of_nonneg
    {d : ℕ} (lam : Fin d → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    firstFactorPartialTrace (Fin d) (Fin d) (schmidtPureMatrix lam) =
      Matrix.diagonal (fun a ↦ (lam a : ℂ)) := by
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun a ↦ (Real.sqrt (lam a) : ℂ)
  calc
    firstFactorPartialTrace (Fin d) (Fin d) (schmidtPureMatrix lam) =
        (Dᴴ * D)ᵀ := by
      ext a b
      simp only [firstFactorPartialTrace_apply, schmidtPureMatrix,
        Matrix.vecMulVec_apply, Pi.star_apply, Matrix.transpose_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      change D i a * star (D i b) = star (D i b) * D i a
      exact mul_comm _ _
    _ = Matrix.diagonal (fun a ↦ (lam a : ℂ)) := by
      simp only [D]
      rw [Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_transpose]
      congr 1
      funext a
      simp only [Pi.star_apply]
      rw [← starRingEnd_apply, Complex.conj_ofReal]
      norm_cast
      exact Real.mul_self_sqrt (hlam a)

end LinearRouting
