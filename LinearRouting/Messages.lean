import LinearRouting.ExactPhaseLocal

/-!
# The message registers

Alice sends the padded qubit and two work registers. Each party sends
its input and the two outcomes of its local measurements in a classical
register. The basis equivalences count the wires in these registers.
-/

namespace LinearRouting.ExactPhase

/-- The padded qubit and the two sent halves of the work pairs. -/
abbrev AliceQuantumMessage (n : ℕ) := BobData (Work n)

/-- A local input and two role-address outcomes. -/
abbrev ClassicalMessage (n : ℕ) := Address n × Source n

abbrev AliceMessage (n : ℕ) := AliceQuantumMessage n × ClassicalMessage n

/-- Bob's quantum register is trivial. His message consists of the classical register. -/
abbrev BobQuantumMessage (_n : ℕ) := Unit

abbrev BobMessage (n : ℕ) := ClassicalMessage n

private def concatBits (m n : ℕ) :
    ((Fin m → ZMod 2) × (Fin n → ZMod 2)) ≃ (Fin (m + n) → ZMod 2) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))

private def oneBit : Fin 2 ≃ (Fin 1 → ZMod 2) :=
  (ZMod.finEquiv 2).toEquiv.trans (Equiv.funUnique (Fin 1) (ZMod 2)).symm

private def labelBits (n : ℕ) : Label n ≃ (Fin (1 + n) → ZMod 2) :=
  ((finTwoEquiv.symm.trans oneBit).prodCongr (Equiv.refl _)).trans (concatBits 1 n)

/-- Lay out each of the two resource registers as its role bit followed by its address. -/
def sourceBits (n : ℕ) : Source n ≃ (Fin (2 * n + 2) → ZMod 2) :=
  ((labelBits n).prodCongr (labelBits n)).trans
    ((concatBits (1 + n) (1 + n)).trans
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)))

private noncomputable def workBits (n : ℕ) : Work n ≃ (Fin (2 ^ n) → ZMod 2) :=
  Equiv.arrowCongr
    (Fintype.equivFinOfCardEq (by simp [Address, ZMod.card])) (Equiv.refl _)

/-- The first wire carries the padded qubit. The remaining wires are the two work registers. -/
noncomputable def aliceQuantumMessageBits (n : ℕ) :
    AliceQuantumMessage n ≃ (Fin (2 ^ (n + 1) + 1) → ZMod 2) :=
  (oneBit.prodCongr (((workBits n).prodCongr (workBits n)).trans
    (concatBits (2 ^ n) (2 ^ n)))).trans
    ((concatBits 1 (2 ^ n + 2 ^ n)).trans
      (Equiv.arrowCongr (finCongr (by rw [pow_succ]; omega)) (Equiv.refl _)))

/-- The first `n` bits carry the sender's input. The two outcomes use `n + 1` bits each. -/
def classicalMessageBits (n : ℕ) : ClassicalMessage n ≃ (Fin (3 * n + 2) → ZMod 2) :=
  ((Equiv.refl _).prodCongr (sourceBits n)).trans
    ((concatBits n (2 * n + 2)).trans
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)))

/-- Bob sends zero qubits, so its quantum basis is the empty bit string. -/
def bobQuantumMessageBits (n : ℕ) : BobQuantumMessage n ≃ (Fin 0 → ZMod 2) where
  toFun _ i := Fin.elim0 i
  invFun _ := ()
  left_inv := by rintro ⟨⟩; rfl
  right_inv := by intro v; funext i; exact Fin.elim0 i

theorem card_aliceQuantumMessage (n : ℕ) :
    Fintype.card (AliceQuantumMessage n) = 2 ^ (2 ^ (n + 1) + 1) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Fintype.card_congr (aliceQuantumMessageBits n)

theorem card_classicalMessage (n : ℕ) : Fintype.card (ClassicalMessage n) = 2 ^ (3 * n + 2) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Fintype.card_congr (classicalMessageBits n)

theorem card_bobQuantumMessage (n : ℕ) : Fintype.card (BobQuantumMessage n) = 2 ^ (0 : ℕ) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Fintype.card_congr (bobQuantumMessageBits n)

end LinearRouting.ExactPhase
