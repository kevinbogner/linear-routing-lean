import Statement
import LinearRouting.Theorem

/-!
# Proof of the statement of Theorem 1

`Statement.lean` states Theorem 1 on registers of bit strings.
This file derives that statement from `LinearRouting.phaseProtocol`, the
strategy of the paper on the registers of its construction. Relabelling the
basis of a register changes neither the recovered qubit nor which parts of a
message are classical, so the properties carry over.
-/

namespace LinearRouting

open Matrix FiniteKrausChannel ExactPhase
open scoped Kronecker ComplexOrder

set_option maxSynthPendingDepth 30
set_option synthInstance.maxSize 4096

noncomputable section

namespace Statement

/-! ## Relabelling the bases of an operation -/

theorem reindex_conj {I O I' O' : Type} [Fintype I] [Fintype I'] (eI : I ≃ I') (eO : O ≃ O')
    (K : Matrix O I ℂ) (ρ : Matrix I I ℂ) :
    Matrix.reindex eO eI K * Matrix.reindex eI eI ρ * (Matrix.reindex eO eI K)ᴴ =
      Matrix.reindex eO eO (K * ρ * Kᴴ) := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

theorem trace_reindex {I I' : Type} [Fintype I] [Fintype I'] (e : I ≃ I') (A : Matrix I I ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i ↦ A i i)

section Channels

variable {I O J P I' O' J' P' : Type}
  [Fintype I] [DecidableEq I] [Fintype O] [Fintype J] [DecidableEq J] [Fintype P]
  [Fintype I'] [DecidableEq I'] [Fintype O'] [Fintype J'] [DecidableEq J'] [Fintype P']

/-- A Kraus family of the main development as an operation of the statement. -/
def Channel.ofKraus {K : Type} [Fintype K] [DecidableEq O]
    (C : FiniteKrausChannel K I O) : Channel I O where
  Index := K
  kraus := C.kraus
  complete := C.completeness

theorem Channel.ofKraus_apply {K : Type} [Fintype K] [DecidableEq O]
    (C : FiniteKrausChannel K I O) (ρ : Matrix I I ℂ) :
    (Channel.ofKraus C).apply ρ = C.action ρ := by
  rw [action_apply]
  rfl

theorem Channel.ofKraus_both {K K' : Type} [Fintype K] [Fintype K'] [DecidableEq O]
    [DecidableEq P] (C : FiniteKrausChannel K I O) (D : FiniteKrausChannel K' J P)
    (ρ : Matrix (I × J) (I × J) ℂ) :
    (Channel.ofKraus C).both (Channel.ofKraus D) ρ = (C.tensor D).action ρ := by
  rw [action_apply, Fintype.sum_prod_type]
  rfl

/-- The operation `C` with relabelled input and output bases. -/
def Channel.relabel (C : Channel I O) (eI : I ≃ I') (eO : O ≃ O') : Channel I' O' where
  Index := C.Index
  kraus k := Matrix.reindex eO eI (C.kraus k)
  complete := by
    ext i j
    have h := congrFun (congrFun C.complete (eI.symm i)) (eI.symm j)
    simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_apply] at h ⊢
    rw [h]
    simp [Matrix.one_apply]

theorem Channel.relabel_apply (C : Channel I O) (eI : I ≃ I') (eO : O ≃ O')
    (ρ : Matrix I I ℂ) :
    (C.relabel eI eO).apply (Matrix.reindex eI eI ρ) = Matrix.reindex eO eO (C.apply ρ) := by
  ext p q
  simp only [Channel.apply, Channel.relabel, reindex_conj]
  simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

theorem Channel.relabel_both (C : Channel I O) (D : Channel J P)
    (eI : I ≃ I') (eO : O ≃ O') (eJ : J ≃ J') (eP : P ≃ P')
    (ρ : Matrix (I × J) (I × J) ℂ) :
    (C.relabel eI eO).both (D.relabel eJ eP)
        (Matrix.reindex (eI.prodCongr eJ) (eI.prodCongr eJ) ρ) =
      Matrix.reindex (eO.prodCongr eP) (eO.prodCongr eP) (C.both D ρ) := by
  ext p q
  simp only [Channel.both, Channel.relabel, Matrix.kroneckerMap_reindex, reindex_conj]
  simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

theorem Channel.relabel_classicalIn {B B' : Type} (C : Channel I O) (eI : I ≃ I')
    (eO : O ≃ O') (part : O → B) (part' : O' → B')
    (hpart : ∀ p q, part' p ≠ part' q → part (eO.symm p) ≠ part (eO.symm q))
    (h : C.ClassicalIn part) : (C.relabel eI eO).ClassicalIn part' := by
  intro ρ p q hpq
  have hρ : ρ = Matrix.reindex eI eI (Matrix.reindex eI.symm eI.symm ρ) := by
    ext i j
    simp
  rw [hρ, Channel.relabel_apply]
  exact h _ _ _ (hpart p q hpq)

end Channels

/-! ## Relabelling the registers of a strategy -/

section Strategies

variable {n : ℕ} {L R AK AM BK BM L' R' AK' AM' BK' BM' : Type}
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype AK] [DecidableEq AK] [Fintype AM] [DecidableEq AM]
  [Fintype BK] [DecidableEq BK] [Fintype BM] [DecidableEq BM]
  [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R']
  [Fintype AK'] [DecidableEq AK'] [Fintype AM'] [DecidableEq AM']
  [Fintype BK'] [DecidableEq BK'] [Fintype BM'] [DecidableEq BM']

/-- The strategy `S` with every register relabelled. -/
def Strategy.relabel (S : Strategy n L R AK AM BK BM) (eL : L ≃ L') (eR : R ≃ R')
    (eAK : AK ≃ AK') (eAM : AM ≃ AM') (eBK : BK ≃ BK') (eBM : BM ≃ BM') :
    Strategy n L' R' AK' AM' BK' BM' where
  shared := Matrix.reindex (eL.prodCongr eR) (eL.prodCongr eR) S.shared
  shared_posSemidef := by
    rw [Matrix.reindex_apply]
    exact S.shared_posSemidef.submatrix _
  shared_trace := (trace_reindex _ _).trans S.shared_trace
  aliceOperation x :=
    (S.aliceOperation x).relabel ((Equiv.refl Qubit).prodCongr eL) (eAK.prodCongr eAM)
  bobOperation y := (S.bobOperation y).relabel eR (eBK.prodCongr eBM)
  aliceRecovery x := (S.aliceRecovery x).relabel (eAK.prodCongr eBM) (Equiv.refl Qubit)
  bobRecovery y := (S.bobRecovery y).relabel (eBK.prodCongr eAM) (Equiv.refl Qubit)

variable (S : Strategy n L R AK AM BK BM) (eL : L ≃ L') (eR : R ≃ R')
  (eAK : AK ≃ AK') (eAM : AM ≃ AM') (eBK : BK ≃ BK') (eBM : BM ≃ BM')

theorem Strategy.relabel_beforeExchange (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    (S.relabel eL eR eAK eAM eBK eBM).beforeExchange x y ρ =
      Matrix.reindex ((eAK.prodCongr eAM).prodCongr (eBK.prodCongr eBM))
        ((eAK.prodCongr eAM).prodCongr (eBK.prodCongr eBM)) (S.beforeExchange x y ρ) := by
  have hstart : (S.relabel eL eR eAK eAM eBK eBM).start ρ =
      Matrix.reindex (((Equiv.refl Qubit).prodCongr eL).prodCongr eR)
        (((Equiv.refl Qubit).prodCongr eL).prodCongr eR) (S.start ρ) := by
    ext ⟨⟨a, l⟩, r⟩ ⟨⟨a', l'⟩, r'⟩
    rfl
  unfold Strategy.beforeExchange
  rw [hstart]
  exact Channel.relabel_both _ _ _ _ _ _ _

theorem Strategy.relabel_aliceRecovers (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    (S.relabel eL eR eAK eAM eBK eBM).aliceRecovers x y ρ = S.aliceRecovers x y ρ := by
  have hholds : (S.relabel eL eR eAK eAM eBK eBM).aliceHolds x y ρ =
      Matrix.reindex (eAK.prodCongr eBM) (eAK.prodCongr eBM) (S.aliceHolds x y ρ) := by
    ext p q
    simp only [Strategy.aliceHolds, Strategy.relabel_beforeExchange, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    exact Fintype.sum_equiv eAM.symm _ _ fun m ↦ Fintype.sum_equiv eBK.symm _ _ fun k ↦ rfl
  unfold Strategy.aliceRecovers
  rw [hholds]
  refine (Channel.relabel_apply _ _ _ _).trans ?_
  ext i j
  rfl

theorem Strategy.relabel_bobRecovers (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    (S.relabel eL eR eAK eAM eBK eBM).bobRecovers x y ρ = S.bobRecovers x y ρ := by
  have hholds : (S.relabel eL eR eAK eAM eBK eBM).bobHolds x y ρ =
      Matrix.reindex (eBK.prodCongr eAM) (eBK.prodCongr eAM) (S.bobHolds x y ρ) := by
    ext p q
    simp only [Strategy.bobHolds, Strategy.relabel_beforeExchange, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    exact Fintype.sum_equiv eAK.symm _ _ fun k ↦ Fintype.sum_equiv eBM.symm _ _ fun m ↦ rfl
  unfold Strategy.bobRecovers
  rw [hholds]
  refine (Channel.relabel_apply _ _ _ _).trans ?_
  ext i j
  rfl

end Strategies

/-! ## The strategy of the paper on the registers of its construction -/

section Construction

variable {n : ℕ}

/-- Alice's kept register and Bob's message, in the order of the main development. -/
def aliceOrder (n : ℕ) : (AliceRetained n × BobMessage n) ≃ AliceReceived n where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun a := (a.1.1, (a.2, a.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bob's kept register and Alice's message, in the order of the main development. -/
def bobOrder (n : ℕ) : (BobRetained n × AliceMessage n) ≃ BobReceived n where
  toFun p := (((p.2.1, p.2.2.2), p.1), p.2.2.1)
  invFun b := (b.1.2, (b.1.1.1, (b.2, b.1.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A protocol of the main development as a strategy of the statement. -/
def ofProtocol (P : OneRoundProtocol n) :
    Strategy n (Fin (SourceDim n)) (Fin (SourceDim n)) (AliceRetained n) (AliceMessage n)
      (BobRetained n) (BobMessage n) where
  shared := productMatrixOfReindexed P.resource.val
  shared_posSemidef := posSemidef_productMatrixOfReindexed P.resource.posSemidef
  shared_trace := (trace_productMatrixOfReindexed _).trans P.resource.trace_eq_one
  aliceOperation x := Channel.ofKraus (P.aliceSend x)
  bobOperation y := Channel.ofKraus (P.bobSend y)
  aliceRecovery x := (Channel.ofKraus (P.aliceDecode x)).relabel (aliceOrder n).symm
    (Equiv.refl Qubit)
  bobRecovery y := (Channel.ofKraus (P.bobDecode y)).relabel (bobOrder n).symm
    (Equiv.refl Qubit)

theorem ofProtocol_beforeExchange (P : OneRoundProtocol n) (x y : Bits n)
    (ρ : Matrix Qubit Qubit ℂ) :
    (ofProtocol P).beforeExchange x y ρ =
      ((P.aliceSend x).tensor (P.bobSend y)).action (P.prepare.action ρ) := by
  have hstart : (ofProtocol P).start ρ = P.prepare.action ρ := by
    rw [P.prepare_action]
    ext ⟨⟨a, l⟩, r⟩ ⟨⟨a', l'⟩, r'⟩
    rfl
  unfold Strategy.beforeExchange
  rw [hstart]
  exact Channel.ofKraus_both _ _ _

theorem ofProtocol_aliceRecovers (P : OneRoundProtocol n) (x y : Bits n)
    (ρ : Matrix Qubit Qubit ℂ) :
    (ofProtocol P).aliceRecovers x y ρ = (P.recoveredByAlice x y).action ρ := by
  have hholds : (ofProtocol P).aliceHolds x y ρ =
      Matrix.reindex (aliceOrder n).symm (aliceOrder n).symm
        ((discardFirst (BobReceived n) (AliceReceived n)).action
          ((P.roundChannel x y).action ρ)) := by
    ext p q
    rw [discardFirst_action, OneRoundProtocol.roundChannel, comp_action, comp_action,
      reindex_action, ← ofProtocol_beforeExchange]
    simp only [Strategy.aliceHolds, Matrix.reindex_apply, Matrix.submatrix_apply,
      firstFactorPartialTrace_apply]
    refine (Fintype.sum_prod_type (fun mk : AliceMessage n × BobRetained n ↦
      (ofProtocol P).beforeExchange x y ρ ((p.1, mk.1), (mk.2, p.2))
        ((q.1, mk.1), (mk.2, q.2)))).symm.trans ?_
    exact Fintype.sum_equiv ((Equiv.prodComm _ _).trans (bobOrder n)) _ _ fun _ ↦ rfl
  unfold Strategy.aliceRecovers OneRoundProtocol.recoveredByAlice
  rw [hholds, comp_action, comp_action]
  refine (Channel.relabel_apply _ _ _ _).trans ?_
  rw [Channel.ofKraus_apply]
  ext i j
  rfl

theorem ofProtocol_bobRecovers (P : OneRoundProtocol n) (x y : Bits n)
    (ρ : Matrix Qubit Qubit ℂ) :
    (ofProtocol P).bobRecovers x y ρ = (P.recoveredByBob x y).action ρ := by
  have hholds : (ofProtocol P).bobHolds x y ρ =
      Matrix.reindex (bobOrder n).symm (bobOrder n).symm
        ((discardSecond (BobReceived n) (AliceReceived n)).action
          ((P.roundChannel x y).action ρ)) := by
    ext p q
    rw [discardSecond_action, OneRoundProtocol.roundChannel, comp_action, comp_action,
      reindex_action, ← ofProtocol_beforeExchange]
    simp only [Strategy.bobHolds, Matrix.reindex_apply, Matrix.submatrix_apply,
      environmentPartialTrace_apply]
    refine (Fintype.sum_prod_type (fun km : AliceRetained n × BobMessage n ↦
      (ofProtocol P).beforeExchange x y ρ ((km.1, p.2), (p.1, km.2))
        ((km.1, q.2), (q.1, km.2)))).symm.trans ?_
    exact Fintype.sum_equiv (aliceOrder n) _ _ fun _ ↦ rfl
  unfold Strategy.bobRecovers OneRoundProtocol.recoveredByBob
  rw [hholds, comp_action, comp_action]
  refine (Channel.relabel_apply _ _ _ _).trans ?_
  rw [Channel.ofKraus_apply]
  ext i j
  rfl

end Construction

/-! ## Registers of bit strings -/

/-- Bit strings of the main development as bit strings of the statement. -/
def toBits (m : ℕ) : (Fin m → ZMod 2) ≃ Bits m :=
  Equiv.arrowCongr (Equiv.refl _) (ZMod.finEquiv 2).symm.toEquiv

/-- Alice's quantum message as a register of `2^(n+1)+1` qubits. -/
def aliceQuantumBits (n : ℕ) : AliceQuantumMessage n ≃ Bits (2 ^ (n + 1) + 1) :=
  (aliceQuantumMessageBits n).trans (toBits _)

/-- A classical message as a register of `3n+2` bits. -/
def classicalBits (n : ℕ) : ClassicalMessage n ≃ Bits (3 * n + 2) :=
  (classicalMessageBits n).trans (toBits _)

/-- The product of EPR amplitudes in the main development is the density
matrix of EPR pairs in the statement. -/
theorem eprPairsMatrix_eq (m : ℕ) : eprPairsMatrix m = eprPairs m := by
  ext p q
  simp only [eprPairsMatrix, eprPairs]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hp : p.1 i = p.2 i <;> by_cases hq : q.1 i = q.2 i <;>
    simp [eprAmplitude, eprPair, hp, hq]

end Statement

open Statement

/-- Theorem 1 of the paper, in the form stated in `Statement.lean`. -/
theorem theorem1 : Statement.Theorem1 := by
  intro n g
  let f : Address n → Address n → Bool := fun x y ↦ decide (g x y = 1)
  have hf := phaseProtocol_guarantees f
  refine ⟨Fintype.card (AliceRetained n), Fintype.card (BobRetained n),
    (ofProtocol (phaseProtocol f)).relabel (eprBasis n) (eprBasis n)
      (Fintype.equivFin (AliceRetained n))
      ((aliceQuantumBits n).prodCongr (classicalBits n))
      (Fintype.equivFin (BobRetained n)) (classicalBits n), ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.eprPairs.trans (eprPairsMatrix_eq _)
  · intro x y hxy ρ
    rw [Strategy.relabel_aliceRecovers, ofProtocol_aliceRecovers]
    exact aliceRecovered_exact f x y (by simp [f, hxy]) ρ
  · intro x y hxy ρ
    rw [Strategy.relabel_bobRecovers, ofProtocol_bobRecovers]
    exact bobRecovered_exact f x y (by simp [f, hxy]) ρ
  · intro x
    refine Channel.relabel_classicalIn _ _ _ (fun o ↦ o.2.2) _ ?_ ?_
    · intro p q hpq h
      exact hpq ((classicalBits n).symm.injective h)
    · intro ρ p q hpq
      exact (congrFun (congrFun (Channel.ofKraus_apply ((phaseProtocol f).aliceSend x) ρ) p)
        q).trans (hf.aliceClassical x ρ p q hpq)
  · intro y
    refine Channel.relabel_classicalIn _ _ _ (fun o ↦ o.2) _ ?_ ?_
    · intro p q hpq h
      exact hpq ((classicalBits n).symm.injective h)
    · intro ρ p q hpq
      exact (congrFun (congrFun (Channel.ofKraus_apply ((phaseProtocol f).bobSend y) ρ) p)
        q).trans (hf.bobClassical y ρ p q hpq)

end

end LinearRouting
