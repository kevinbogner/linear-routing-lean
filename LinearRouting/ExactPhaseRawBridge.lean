import LinearRouting.SchmidtResource
import LinearRouting.NormalizedSchmidtRoutingProtocol
import LinearRouting.OneRoundRoutingProcess

/-!
# Realizing a normalized Schmidt router in the raw routing model

The raw process uses the same Schmidt state and local isometries. Its
receiver registers use a different tensor-factor order, which the decoder
undoes before applying the original recovery.
-/

namespace LinearRouting.ExactPhase.SchmidtRaw

open Matrix FiniteKrausChannel
open scoped BigOperators Kronecker

variable {X Y RA RB : Type*} [Fintype RA] [Fintype RB]
variable {d n m a b : ℕ} {f : X → Y → Bool}
variable (P : NormalizedSchmidtRoutingProtocol X Y RA RB d n m a b f)

/-- The Schmidt state in the standard raw resource carrier. -/
noncomputable def resource : DensityMatrix (d * d) :=
  densityOfProductMatrix (schmidtPureMatrix P.lam) (schmidtPureMatrix_posSemidef _)
    (by rw [trace_schmidtPureMatrix _ P.lam_nonnegative]; exact_mod_cast P.lam_sum)

private theorem resource_product :
    productMatrixOfReindexed (resource P).val = schmidtPureMatrix P.lam := by
  exact productMatrixOfReindexed_reindexProductMatrix _

private noncomputable def alice (x : X) :=
  ofIsometry (P.alice x) (P.alice_isometry x)

private noncomputable def bob (y : Y) :=
  ofIsometry (P.bob y) (P.bob_isometry y)

private def bobProductOrder (n m : ℕ) : (Fin m × Fin n) ≃ (Fin n × Fin m) :=
  Equiv.prodComm _ _

private def bobRecoveryOrder (n m : ℕ) : Fin (m * n) ≃ Fin (n * m) :=
  finProdFinEquiv.symm.trans ((bobProductOrder n m).trans finProdFinEquiv)

private def rawOutputOrder (n m a b : ℕ) :
    ((Fin n × Fin m) × (Fin a × Fin b)) ≃ ((Fin a × Fin b) × (Fin m × Fin n)) :=
  (Equiv.prodComm _ _).trans ((Equiv.refl _).prodCongr (bobProductOrder n m).symm)

/-- A normalized Schmidt router as a realized raw one-round process. -/
noncomputable def toProcess :
    OneRoundRoutingProcess X Y (Fin 1) (Fin 1)
      (OneRoundRoutingCanonicalGlobalKraus (Fin 1) (Fin 1) d d)
      RA (Fin 1 × RB) d d a n m b :=
  OneRoundRoutingProcess.ofCanonicalGlobal (resource P) (alice P) (bob P)
    P.recoverAlice
    (fun x y => (P.recoverBob x y).comp (FiniteKrausChannel.reindex (bobRecoveryOrder n m)))

/-- The raw process is charged at most its local Schmidt dimension. -/
theorem resourceDimension_le : sharedResourceDimension (toProcess P).rhoLR ≤ d :=
  (min_le_left _ _).trans (bipartiteLeftMarginal (resource P)).val.rank_le_width

/-- Positive Schmidt weights occupy all resource basis states on both sides. -/
theorem resourceDimension_eq_of_pos (hpos : ∀ r, 0 < P.lam r) :
    sharedResourceDimension (toProcess P).rhoLR = d := by
  have hleft : (bipartiteLeftMarginal (resource P)).val =
      Matrix.diagonal (fun r => (P.lam r : ℂ)) := by
    change environmentPartialTrace (Fin d) (Fin d) (productMatrixOfReindexed (resource P).val) = _
    rw [resource_product, environmentPartialTrace_schmidtPureMatrix_of_nonneg _ P.lam_nonnegative]
  have hright : (bipartiteRightMarginal (resource P)).val =
      Matrix.diagonal (fun r => (P.lam r : ℂ)) := by
    change firstFactorPartialTrace (Fin d) (Fin d) (productMatrixOfReindexed (resource P).val) = _
    rw [resource_product, firstFactorPartialTrace_schmidtPureMatrix_of_nonneg _ P.lam_nonnegative]
  change sharedResourceDimension (resource P) = d
  unfold sharedResourceDimension
  rw [hleft, hright, Matrix.rank_diagonal, min_self]
  let e : {r : Fin d // (P.lam r : ℂ) ≠ 0} ≃ Fin d :=
    { toFun := Subtype.val
      invFun := fun r => ⟨r, by exact_mod_cast (hpos r).ne'⟩
      left_inv := fun r => by ext; rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr e

/-- Appending the shared Schmidt resource agrees with its isometric embedding. -/
theorem inputMatrix_eq (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    oneRoundRoutingInputMatrix (resource P) Q =
      schmidtProtocolInputIsometry P.lam * Q * (schmidtProtocolInputIsometry P.lam)ᴴ := by
  ext ⟨⟨q, l⟩, r⟩ ⟨⟨q', l'⟩, r'⟩
  simp only [oneRoundRoutingInputMatrix, resource_product, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  change Q q q' * schmidtPureMatrix P.lam (l, r) (l', r') = _
  simp only [schmidtPureMatrix, schmidtVector, Matrix.vecMulVec_apply, Pi.star_apply]
  by_cases h : l = r <;> by_cases h' : l' = r' <;>
    simp [h, h', schmidtProtocolInputIsometry, Matrix.mul_apply,
      Matrix.conjTranspose_apply, ite_mul, Finset.sum_ite_eq]
  fin_cases q' <;> simp <;> ring

private theorem reindex_conjugation {I O O' : Type*} [Fintype I]
    (e : O ≃ O') (V : Matrix O I ℂ) (Q : Matrix I I ℂ) :
    Matrix.reindex e e (V * Q * Vᴴ) =
      Matrix.reindex e (Equiv.refl I) V * Q * (Matrix.reindex e (Equiv.refl I) V)ᴴ := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem localTensor_action (x : X) (y : Y)
    (Q : Matrix ((Fin 2 × Fin d) × Fin d) ((Fin 2 × Fin d) × Fin d) ℂ) :
    (((alice P x).tensor (bob P y)).action Q) =
      schmidtProtocolLocalTensorIsometry P.alice P.bob x y * Q *
        (schmidtProtocolLocalTensorIsometry P.alice P.bob x y)ᴴ := by
  simp [FiniteKrausChannel.action_apply, tensor_kraus, alice, bob, ofIsometry,
    schmidtProtocolLocalTensorIsometry]

private theorem realizedOutput_eq (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    oneRoundRoutingRealizedOutputMatrix (resource P) (alice P) (bob P) x y Q =
      Matrix.reindex (rawOutputOrder n m a b) (rawOutputOrder n m a b)
        ((schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
          P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q) := by
  rw [oneRoundRoutingRealizedOutputMatrix, localTensor_action, inputMatrix_eq]
  have hmul : let E := schmidtProtocolInputIsometry P.lam
      let L := schmidtProtocolLocalTensorIsometry P.alice P.bob x y
      L * (E * Q * Eᴴ) * Lᴴ = (L * E) * Q * (L * E)ᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hmul, reindex_conjugation]
  unfold schmidtProtocolGlobalChannel
  rw [ofIsometry_action, reindex_conjugation]
  rfl

/-- Alice receives the same reduced channel in either model. -/
theorem alicePreRecovery_action_eq (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((toProcess P).alicePreRecovery x y).action Q =
      (schmidtProtocolAliceReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q := by
  rw [OneRoundRoutingProcess.alicePreRecovery_action]
  change reindexProductMatrix (environmentPartialTrace _ _
    (oneRoundRoutingRealizedOutputMatrix (resource P) (alice P) (bob P) x y Q)) = _
  rw [realizedOutput_eq, schmidtProtocolAliceReducedFinChannel,
    schmidtProtocolAliceReducedChannel, comp_action, productReindexChannel_action,
    comp_action, discardFirst_action]
  congr 1
  ext i j
  simp only [environmentPartialTrace_apply, firstFactorPartialTrace_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp (bobProductOrder n m) (fun k =>
    (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
      P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q (k, i) (k, j))

/-- Undoing Bob's tensor-factor swap gives his original reduced channel. -/
private theorem bobPreRecovery_action_eq (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (FiniteKrausChannel.reindex (bobRecoveryOrder n m)).action
      (((toProcess P).bobPreRecovery x y).action Q) =
      (schmidtProtocolBobReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q := by
  rw [OneRoundRoutingProcess.bobPreRecovery_action]
  change (FiniteKrausChannel.reindex (bobRecoveryOrder n m)).action
    (reindexProductMatrix (firstFactorPartialTrace _ _
      (oneRoundRoutingRealizedOutputMatrix (resource P) (alice P) (bob P) x y Q))) = _
  rw [realizedOutput_eq, reindex_action, schmidtProtocolBobReducedFinChannel,
    schmidtProtocolBobReducedChannel, comp_action, productReindexChannel_action,
    comp_action, discardSecond_action]
  ext i j
  simp [reindexProductMatrix, Matrix.reindex_apply, rawOutputOrder, bobRecoveryOrder,
    bobProductOrder]

/-- Alice's recovered action agrees on every matrix, including when her
decoder's branch was not selected. -/
theorem aliceRecovered_action_eq (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (((toProcess P).recoverAlice x y).comp ((toProcess P).alicePreRecovery x y)).action Q =
      ((P.recoverAlice x y).comp
        (schmidtProtocolAliceReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
          P.alice P.bob P.alice_isometry P.bob_isometry x y)).action Q := by
  simp only [comp_action, alicePreRecovery_action_eq]
  rfl

/-- Bob's recovered action agrees on every matrix, including when his
decoder's branch was not selected. -/
theorem bobRecovered_action_eq (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (((toProcess P).recoverBob x y).comp ((toProcess P).bobPreRecovery x y)).action Q =
      ((P.recoverBob x y).comp
        (schmidtProtocolBobReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
          P.alice P.bob P.alice_isometry P.bob_isometry x y)).action Q := by
  simp only [comp_action]
  change ((P.recoverBob x y).comp (FiniteKrausChannel.reindex (bobRecoveryOrder n m))).action
    (((toProcess P).bobPreRecovery x y).action Q) = _
  rw [comp_action, bobPreRecovery_action_eq]

end LinearRouting.ExactPhase.SchmidtRaw
