import LinearRouting.FiniteKrausReindex
import LinearRouting.NormalizedSchmidtRoutingProtocol

/-!
# Exact product-indexed Schmidt routers in the normalized model

Independent changes of basis on the four local output factors convert
product-indexed local encoders to the finite carriers of the normalized
model. The receivers undo the corresponding basis changes before decoding.
Neither the Schmidt weights nor the recovered channel actions change.
-/

namespace LinearRouting.ExactPhase

open Matrix FiniteKrausChannel
open scoped BigOperators

/-- An exact Schmidt router using product-indexed local outputs. -/
structure ProductSchmidtExactRouter
    (X Y Akeep Xmsg Ykeep Bmsg RA RB : Type*)
    [Fintype Akeep] [DecidableEq Akeep] [Fintype Xmsg] [DecidableEq Xmsg]
    [Fintype Ykeep] [DecidableEq Ykeep] [Fintype Bmsg] [DecidableEq Bmsg]
    [Fintype RA] [Fintype RB] (d : ℕ) (f : X → Y → Bool) where
  lam : Fin d → ℝ
  lam_nonnegative : ∀ r, 0 ≤ lam r
  lam_sum : ∑ r, lam r = 1
  alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ
  bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ
  alice_isometry : ∀ x, (alice x)ᴴ * alice x = 1
  bob_isometry : ∀ y, (bob y)ᴴ * bob y = 1
  recoverAlice : X → Y → FiniteKrausChannel RA (Akeep × Bmsg) (Fin 2)
  recoverBob : X → Y → FiniteKrausChannel RB (Xmsg × Ykeep) (Fin 2)
  alice_exact : ∀ x y, f x y = false → ∀ Q : Matrix (Fin 2) (Fin 2) ℂ,
    ((recoverAlice x y).comp
      ((discardFirst (Xmsg × Ykeep) (Akeep × Bmsg)).comp
        (schmidtProtocolGlobalChannel lam lam_nonnegative lam_sum
          alice bob alice_isometry bob_isometry x y))).action Q = Q
  bob_exact : ∀ x y, f x y = true → ∀ Q : Matrix (Fin 2) (Fin 2) ℂ,
    ((recoverBob x y).comp
      ((discardSecond (Xmsg × Ykeep) (Akeep × Bmsg)).comp
        (schmidtProtocolGlobalChannel lam lam_nonnegative lam_sum
          alice bob alice_isometry bob_isometry x y))).action Q = Q

namespace ProductSchmidtExactRouter

variable {X Y Akeep Xmsg Ykeep Bmsg RA RB : Type*}
variable [Fintype Akeep] [DecidableEq Akeep] [Fintype Xmsg] [DecidableEq Xmsg]
variable [Fintype Ykeep] [DecidableEq Ykeep] [Fintype Bmsg] [DecidableEq Bmsg]
variable [Fintype RA] [Fintype RB] {d : ℕ} {f : X → Y → Bool}
variable (P : ProductSchmidtExactRouter X Y Akeep Xmsg Ykeep Bmsg RA RB d f)

private noncomputable def finitePairBasis (U V : Type*) [Fintype U] [Fintype V] :
    (U × V) ≃ Fin (Fintype.card U) × Fin (Fintype.card V) :=
  (Fintype.equivFin U).prodCongr (Fintype.equivFin V)

private noncomputable def recoveryBasis (U V : Type*) [Fintype U] [Fintype V] :
    Fin (Fintype.card U * Fintype.card V) ≃ U × V :=
  finProdFinEquiv.symm.trans (finitePairBasis U V).symm

private theorem reindex_rows_isometry {I O O' : Type*}
    [Fintype O] [Fintype O'] [DecidableEq I]
    (e : O ≃ O') (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    (Matrix.reindex e (Equiv.refl I) V)ᴴ * Matrix.reindex e (Equiv.refl I) V = 1 := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv _ _ _ e.symm _, hV, Matrix.submatrix_one_equiv]

private noncomputable def aliceFin (x : X) :
    Matrix (Fin (Fintype.card Akeep) × Fin (Fintype.card Xmsg)) (Fin 2 × Fin d) ℂ :=
  Matrix.reindex (finitePairBasis Akeep Xmsg) (Equiv.refl _) (P.alice x)

private noncomputable def bobFin (y : Y) :
    Matrix (Fin (Fintype.card Ykeep) × Fin (Fintype.card Bmsg)) (Fin d) ℂ :=
  Matrix.reindex (finitePairBasis Ykeep Bmsg) (Equiv.refl _) (P.bob y)

private theorem aliceFin_isometry (x : X) : (P.aliceFin x)ᴴ * P.aliceFin x = 1 :=
  reindex_rows_isometry _ _ (P.alice_isometry x)

private theorem bobFin_isometry (y : Y) : (P.bobFin y)ᴴ * P.bobFin y = 1 :=
  reindex_rows_isometry _ _ (P.bob_isometry y)

private noncomputable def recoverAliceFin (x : X) (y : Y) :
    FiniteKrausChannel (Fin 1 × RA) (Fin (Fintype.card Akeep * Fintype.card Bmsg)) (Fin 2) :=
  (P.recoverAlice x y).comp (FiniteKrausChannel.reindex (recoveryBasis Akeep Bmsg))

private noncomputable def recoverBobFin (x : X) (y : Y) :
    FiniteKrausChannel (Fin 1 × RB) (Fin (Fintype.card Xmsg * Fintype.card Ykeep)) (Fin 2) :=
  (P.recoverBob x y).comp (FiniteKrausChannel.reindex (recoveryBasis Xmsg Ykeep))

private theorem globalIsometry_reindex_apply (x : X) (y : Y)
    (p : (Fin (Fintype.card Xmsg) × Fin (Fintype.card Ykeep)) ×
      (Fin (Fintype.card Akeep) × Fin (Fintype.card Bmsg))) (q : Fin 2) :
    schmidtProtocolGlobalIsometry P.lam P.aliceFin P.bobFin x y p q =
      schmidtProtocolGlobalIsometry P.lam P.alice P.bob x y
        ((finitePairBasis Xmsg Ykeep).symm p.1, (finitePairBasis Akeep Bmsg).symm p.2) q := by
  rcases p with ⟨⟨m, k⟩, a, b⟩
  rw [schmidtProtocolGlobalIsometry_apply, schmidtProtocolGlobalIsometry_apply]
  rfl

private theorem globalAction_reindex_apply (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (p p' : (Fin (Fintype.card Xmsg) × Fin (Fintype.card Ykeep)) ×
      (Fin (Fintype.card Akeep) × Fin (Fintype.card Bmsg))) :
    (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
      P.aliceFin P.bobFin P.aliceFin_isometry P.bobFin_isometry x y).action Q p p' =
    (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
      P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q
      ((finitePairBasis Xmsg Ykeep).symm p.1, (finitePairBasis Akeep Bmsg).symm p.2)
      ((finitePairBasis Xmsg Ykeep).symm p'.1, (finitePairBasis Akeep Bmsg).symm p'.2) := by
  simp only [schmidtProtocolGlobalChannel, ofIsometry_action, Matrix.mul_apply,
    Matrix.conjTranspose_apply, P.globalIsometry_reindex_apply]

private theorem inverseProductReindex_action {U V : Type*} [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V]
    (M : Matrix (Fin (Fintype.card U) × Fin (Fintype.card V))
      (Fin (Fintype.card U) × Fin (Fintype.card V)) ℂ) :
    (FiniteKrausChannel.reindex (recoveryBasis U V)).action
      ((productReindexChannel (Fintype.card U) (Fintype.card V)).action M) =
      Matrix.reindex (finitePairBasis U V).symm (finitePairBasis U V).symm M := by
  rw [FiniteKrausChannel.reindex_action, productReindexChannel_action]
  ext p q
  simp [recoveryBasis, reindexProductMatrix, Matrix.reindex_apply]

private theorem aliceReduced_reindex_action
    (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (FiniteKrausChannel.reindex (recoveryBasis Akeep Bmsg)).action
      ((schmidtProtocolAliceReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.aliceFin P.bobFin P.aliceFin_isometry P.bobFin_isometry x y).action Q) =
      ((discardFirst (Xmsg × Ykeep) (Akeep × Bmsg)).comp
        (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
          P.alice P.bob P.alice_isometry P.bob_isometry x y)).action Q := by
  rw [schmidtProtocolAliceReducedFinChannel, comp_action, inverseProductReindex_action]
  ext a a'
  simp only [schmidtProtocolAliceReducedChannel, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, comp_action, discardFirst_action, firstFactorPartialTrace_apply,
    P.globalAction_reindex_apply, Equiv.symm_apply_apply]
  exact Equiv.sum_comp (finitePairBasis Xmsg Ykeep).symm (fun i =>
    (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
      P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q (i, a) (i, a'))

private theorem bobReduced_reindex_action
    (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (FiniteKrausChannel.reindex (recoveryBasis Xmsg Ykeep)).action
      ((schmidtProtocolBobReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.aliceFin P.bobFin P.aliceFin_isometry P.bobFin_isometry x y).action Q) =
      ((discardSecond (Xmsg × Ykeep) (Akeep × Bmsg)).comp
        (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
          P.alice P.bob P.alice_isometry P.bob_isometry x y)).action Q := by
  rw [schmidtProtocolBobReducedFinChannel, comp_action, inverseProductReindex_action]
  ext b b'
  simp only [schmidtProtocolBobReducedChannel, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, comp_action, discardSecond_action, environmentPartialTrace_apply,
    P.globalAction_reindex_apply, Equiv.symm_apply_apply]
  exact Equiv.sum_comp (finitePairBasis Akeep Bmsg).symm (fun i =>
    (schmidtProtocolGlobalChannel P.lam P.lam_nonnegative P.lam_sum
      P.alice P.bob P.alice_isometry P.bob_isometry x y).action Q (b, i) (b', i))

private theorem aliceFin_exact (x : X) (y : Y) (h : f x y = false)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((P.recoverAliceFin x y).comp
      (schmidtProtocolAliceReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.aliceFin P.bobFin P.aliceFin_isometry P.bobFin_isometry x y)).action Q = Q := by
  simp only [recoverAliceFin, comp_action, P.aliceReduced_reindex_action]
  simpa only [comp_action] using P.alice_exact x y h Q

private theorem bobFin_exact (x : X) (y : Y) (h : f x y = true)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((P.recoverBobFin x y).comp
      (schmidtProtocolBobReducedFinChannel P.lam P.lam_nonnegative P.lam_sum
        P.aliceFin P.bobFin P.aliceFin_isometry P.bobFin_isometry x y)).action Q = Q := by
  simp only [recoverBobFin, comp_action, P.bobReduced_reindex_action]
  simpa only [comp_action] using P.bob_exact x y h Q

/-- Reindex the local carriers to the existing normalized protocol model. -/
noncomputable def toNormalized :
    NormalizedSchmidtRoutingProtocol X Y (Fin 1 × RA) (Fin 1 × RB) d
      (Fintype.card Xmsg) (Fintype.card Ykeep) (Fintype.card Akeep) (Fintype.card Bmsg) f where
  lam := P.lam
  lam_nonnegative := P.lam_nonnegative
  lam_sum := P.lam_sum
  alice := P.aliceFin
  bob := P.bobFin
  alice_isometry := P.aliceFin_isometry
  bob_isometry := P.bobFin_isometry
  recoverAlice := P.recoverAliceFin
  recoverBob := P.recoverBobFin
  alice_correct := P.aliceFin_exact
  bob_correct := P.bobFin_exact

/-- Alice's selected decoder remains exact after reindexing. -/
theorem toNormalized_alice_exact (x : X) (y : Y) (h : f x y = false)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((P.toNormalized.recoverAlice x y).comp
      (schmidtProtocolAliceReducedFinChannel P.toNormalized.lam
        P.toNormalized.lam_nonnegative P.toNormalized.lam_sum
        P.toNormalized.alice P.toNormalized.bob P.toNormalized.alice_isometry
        P.toNormalized.bob_isometry x y)).action Q = Q :=
  P.aliceFin_exact x y h Q

/-- Bob's selected decoder remains exact after reindexing. -/
theorem toNormalized_bob_exact (x : X) (y : Y) (h : f x y = true)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((P.toNormalized.recoverBob x y).comp
      (schmidtProtocolBobReducedFinChannel P.toNormalized.lam
        P.toNormalized.lam_nonnegative P.toNormalized.lam_sum
        P.toNormalized.alice P.toNormalized.bob P.toNormalized.alice_isometry
        P.toNormalized.bob_isometry x y)).action Q = Q :=
  P.bobFin_exact x y h Q

end ProductSchmidtExactRouter

end LinearRouting.ExactPhase
