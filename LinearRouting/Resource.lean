import LinearRouting.ExactPhaseRouter
import LinearRouting.Messages

/-!
# The shared Bell pairs

The router's uniform Schmidt state is the tensor product of its
individual Bell pairs, expressed in the computational basis.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

noncomputable section

/-- A computational-basis string for a register of qubits. -/
abbrev QubitString (m : ℕ) := Fin m → Fin 2

/-- Both resource registers have the same computational basis, with the role
bit and address of each block laid out consecutively. -/
def eprBasis (n : ℕ) : Fin (SourceDim n) ≃ QubitString (2 * n + 2) :=
  (sourceBasis n).trans ((sourceBits n).trans
    (Equiv.arrowCongr (Equiv.refl _) (ZMod.finEquiv 2).symm.toEquiv))

/-- The density matrix of independent EPR pairs, in the basis that groups
the qubits by party. Each entry is a product of single-pair density entries. -/
def eprPairsMatrix (m : ℕ) :
    Matrix (QubitString m × QubitString m) (QubitString m × QubitString m) ℂ :=
  fun p q ↦ ∏ i : Fin m,
    eprAmplitude (p.1 i) (p.2 i) * star (eprAmplitude (q.1 i) (q.2 i))

private theorem eprPairsMatrix_apply (m : ℕ) (p q : QubitString m × QubitString m) :
    eprPairsMatrix m p q =
      if p.1 = p.2 ∧ q.1 = q.2 then ((2 ^ m : ℕ) : ℂ)⁻¹ else 0 := by
  by_cases hp : p.1 = p.2
  · by_cases hq : q.1 = q.2
    · simp [eprPairsMatrix, eprAmplitude, hp, hq]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
      simp only [eprPairsMatrix, hp, hq, and_false, if_false]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [eprAmplitude, hi]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
    simp only [eprPairsMatrix, hp, false_and, if_false]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [eprAmplitude, hi]

/-- Uniform Schmidt weights are the computational-basis weights of EPR pairs. -/
theorem uniformSchmidt_eq_eprPairs {m : ℕ} (e : Fin (2 ^ m) ≃ QubitString m) :
    Matrix.reindex (e.prodCongr e) (e.prodCongr e)
        (schmidtPureMatrix (fun _ : Fin (2 ^ m) ↦ ((2 ^ m : ℕ) : ℝ)⁻¹)) =
      eprPairsMatrix m := by
  ext p q
  rw [eprPairsMatrix_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, schmidtPureMatrix,
    Matrix.vecMulVec_apply, Pi.star_apply, schmidtVector, Equiv.apply_eq_iff_eq]
  change (if p.1 = p.2 then flatAmplitude (2 ^ m) else 0) *
      star (if q.1 = q.2 then flatAmplitude (2 ^ m) else 0) = _
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [hp, hq, flatAmplitude_mul_self]

/-- The protocol's actual shared density matrix is the tensor product of
one EPR pair for each of the 2n+2 qubits on either side of the cut. -/
theorem exactPhaseRoutingProcess_resource_eq_eprPairs {n : ℕ}
    (f : Address n → Address n → Bool) :
    Matrix.reindex ((eprBasis n).prodCongr (eprBasis n))
        ((eprBasis n).prodCongr (eprBasis n))
        (productMatrixOfReindexed (exactPhaseRoutingProcess f).rhoLR.val) =
      eprPairsMatrix (2 * n + 2) := by
  change Matrix.reindex _ _
      (productMatrixOfReindexed
        (reindexProductMatrix (schmidtPureMatrix (exactPhaseRouterNormalized f).lam))) = _
  rw [productMatrixOfReindexed_reindexProductMatrix]
  exact uniformSchmidt_eq_eprPairs (eprBasis n)

end

end LinearRouting.ExactPhase
