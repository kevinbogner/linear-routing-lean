import LinearRouting.FiniteKrausTensor
import LinearRouting.BipartiteDensity

/-!
# Exact recovery and finite reference systems

A channel acts on each block indexed by the reference. Equality of channel
actions therefore preserves every finite joint input and reference state.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

/-- Density matrices are determined by their matrix value. -/
@[ext]
theorem DensityMatrix.ext_val {n : ℕ} {rho sigma : DensityMatrix n}
    (h : rho.val = sigma.val) : rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          simp only at h
          subst sigma
          rfl

namespace FiniteKrausChannel

universe uK uL

variable {K : Type uK} [Fintype K]
variable {L : Type uL} [Fintype L]

/-- Apply a channel to one factor of a density matrix while retaining an
arbitrary finite reference system. -/
noncomputable def amplifiedMapDensity {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m)) (referenceDim : ℕ)
    (rho : DensityMatrix (n * referenceDim)) :
    DensityMatrix (m * referenceDim) :=
  densityOfProductMatrix
    ((Phi.tensor
      (identity : FiniteKrausChannel (Fin 1)
        (Fin referenceDim) (Fin referenceDim))).action
      (productMatrixOfReindexed rho.val))
    ((Phi.tensor
      (identity : FiniteKrausChannel (Fin 1)
        (Fin referenceDim) (Fin referenceDim))).action_posSemidef
      (posSemidef_productMatrixOfReindexed rho.posSemidef))
    (by
      rw [(Phi.tensor
        (identity : FiniteKrausChannel (Fin 1)
          (Fin referenceDim) (Fin referenceDim))).trace_action,
        trace_productMatrixOfReindexed, rho.trace_eq_one])

@[simp]
theorem amplifiedMapDensity_val {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m)) (referenceDim : ℕ)
    (rho : DensityMatrix (n * referenceDim)) :
    (Phi.amplifiedMapDensity referenceDim rho).val =
      reindexProductMatrix
        ((Phi.tensor
          (identity : FiniteKrausChannel (Fin 1)
            (Fin referenceDim) (Fin referenceDim))).action
          (productMatrixOfReindexed rho.val)) := rfl

/-- Pointwise inequality form of full, unhalved diamond closeness for two
finite Kraus channels. -/
def FullDiamondErrorAtMost {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (Psi : FiniteKrausChannel L (Fin n) (Fin m))
    (epsilon : ℝ) : Prop :=
  (∀ rho : DensityMatrix n,
      densityTraceDistance (Phi.mapDensity rho) (Psi.mapDensity rho) ≤
        epsilon) ∧
    ∀ (referenceDim : ℕ) (_href : 0 < referenceDim)
        (rho : DensityMatrix (n * referenceDim)),
      densityTraceDistance
        (Phi.amplifiedMapDensity referenceDim rho)
        (Psi.amplifiedMapDensity referenceDim rho) ≤ epsilon

universe uT uI uO uR

variable {T : Type uT} [Fintype T]

/-- A matrix entry of a channel amplified by the identity is the
corresponding entry of the channel applied to a reference-indexed block. -/
theorem tensor_identity_action_apply
    {I : Type uI} {O : Type uO} {R : Type uR}
    [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    [Fintype R] [DecidableEq R]
    (Phi : FiniteKrausChannel K I O)
    (M : Matrix (I × R) (I × R) ℂ)
    (o o' : O) (r r' : R) :
    ((Phi.tensor
      (identity : FiniteKrausChannel (Fin 1)
        R R)).action M)
        (o, r) (o', r') =
      Phi.action (fun i i' ↦ M (i, r) (i', r')) o o' := by
  rw [action_apply, action_apply, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply, tensor_kraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [identity, ofIsometry, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro i' _hi'
  rw [Finset.sum_eq_single r']
  · simp
  · intro s _hs hsr
    simp [Ne.symm hsr]
  · intro hr'
    exact (hr' (Finset.mem_univ _)).elim

/-- Equality of channel actions is stable under amplification by every
finite identity reference. -/
theorem tensor_identity_action_eq_of_action_eq
    {n m referenceDim : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (Psi : FiniteKrausChannel L (Fin n) (Fin m))
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Phi.action M = Psi.action M)
    (M : Matrix (Fin n × Fin referenceDim)
      (Fin n × Fin referenceDim) ℂ) :
    (Phi.tensor
      (identity : FiniteKrausChannel (Fin 1)
        (Fin referenceDim) (Fin referenceDim))).action M =
      (Psi.tensor
        (identity : FiniteKrausChannel (Fin 1)
          (Fin referenceDim) (Fin referenceDim))).action M := by
  ext o o'
  rcases o with ⟨i, r⟩
  rcases o' with ⟨i', r'⟩
  rw [tensor_identity_action_apply, tensor_identity_action_apply,
    h (fun j j' ↦ M (j, r) (j', r'))]

/-- Equality on all matrices gives equality of bundled density outputs. -/
theorem mapDensity_eq_of_action_eq
    {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (Psi : FiniteKrausChannel L (Fin n) (Fin m))
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Phi.action M = Psi.action M)
    (rho : DensityMatrix n) :
    Phi.mapDensity rho = Psi.mapDensity rho := by
  apply DensityMatrix.ext_val
  exact h rho.val

/-- Equality on all matrices gives equality of every finite-reference
amplified density output. -/
theorem amplifiedMapDensity_eq_of_action_eq
    {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (Psi : FiniteKrausChannel L (Fin n) (Fin m))
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Phi.action M = Psi.action M)
    (referenceDim : ℕ) (rho : DensityMatrix (n * referenceDim)) :
    Phi.amplifiedMapDensity referenceDim rho =
      Psi.amplifiedMapDensity referenceDim rho := by
  apply DensityMatrix.ext_val
  simp only [amplifiedMapDensity_val]
  congr 1
  exact tensor_identity_action_eq_of_action_eq Phi Psi h
    (productMatrixOfReindexed rho.val)

/-- Full diamond-error correctness likewise depends only on the channel
actions, not on their Kraus representations. -/
theorem fullDiamondErrorAtMost_of_action_eq
    {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (Phi' : FiniteKrausChannel L (Fin n) (Fin m))
    (Psi : FiniteKrausChannel T (Fin n) (Fin m))
    (epsilon : ℝ)
    (hPhi : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Phi'.action M = Phi.action M)
    (hcorrect : FullDiamondErrorAtMost Phi Psi epsilon) :
    FullDiamondErrorAtMost Phi' Psi epsilon := by
  constructor
  · intro rho
    rw [mapDensity_eq_of_action_eq Phi' Phi hPhi rho]
    exact hcorrect.1 rho
  · intro referenceDim href rho
    rw [amplifiedMapDensity_eq_of_action_eq
      Phi' Phi hPhi referenceDim rho]
    exact hcorrect.2 referenceDim href rho

end FiniteKrausChannel

end LinearRouting
