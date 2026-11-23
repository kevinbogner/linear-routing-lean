import LinearRouting.ExactPhaseRouter
import LinearRouting.Messages
import LinearRouting.RecordedChannel

/-!
# The measured one-round protocol

Each pre-exchange channel acts on its own input and half of the shared
state. It measures its local outcomes and includes its input in the outgoing
classical register. Each recovery reads the input label received in the
exchange and acts on that party's own registers only.
-/

namespace LinearRouting.ExactPhase

open Matrix FiniteKrausChannel
open scoped Kronecker

set_option maxSynthPendingDepth 30
set_option synthInstance.maxSize 4096

noncomputable section

variable {n : ℕ}

abbrev AliceRetained (n : ℕ) := AliceKeep (Label n) (Work n)
abbrev BobRetained (n : ℕ) := Source n
abbrev AliceReceived (n : ℕ) := PhaseAlice n × Address n
abbrev BobReceived (n : ℕ) := PhaseBob n × Address n

def aliceWireOrder (n : ℕ) :
    ((AliceRetained n × AliceSend (Label n) (Work n)) × Address n) ≃
      (AliceRetained n × AliceMessage n) where
  toFun p := (p.1.1, p.1.2.1, p.2, p.1.2.2)
  invFun p := ((p.1, p.2.1, p.2.2.2), p.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def bobWireOrder (n : ℕ) :
    ((BobRetained n × Source n) × Address n) ≃ (BobRetained n × BobMessage n) where
  toFun p := (p.1.1, p.2, p.1.2)
  invFun p := ((p.1, p.2.2), p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Alice keeps her key, work halves and outcomes. She sends the padded
qubit, the other work halves, her input, and her measured outcomes. -/
def aliceSendChannel (f : Address n → Address n → Bool) (x : Address n) :
    FiniteKrausChannel (Source n × Fin 1) (Fin 2 × Fin (SourceDim n))
      (AliceRetained n × AliceMessage n) :=
  (FiniteKrausChannel.reindex (aliceWireOrder n)).comp
    (recorded (phaseAlice f x) (phaseAlice_isometry f x) (fun p ↦ p.2.2) x)

/-- Bob sends his input and his two measured outcomes, keeping a copy of
the outcomes. His message has no quantum register. -/
def bobSendChannel (y : Address n) :
    FiniteKrausChannel (Source n × Fin 1) (Fin (SourceDim n))
      (BobRetained n × BobMessage n) :=
  (FiniteKrausChannel.reindex (bobWireOrder n)).comp
    (recorded (phaseBob y) (phaseBob_isometry y) Prod.snd y)

def exchange (n : ℕ) :
    ((AliceRetained n × AliceMessage n) × (BobRetained n × BobMessage n)) ≃
      (BobReceived n × AliceReceived n) where
  toFun p := ((((p.1.2.1, p.1.2.2.2), p.2.1), p.1.2.2.1),
    ((p.1.1, p.2.2.2), p.2.2.1))
  invFun p := ((p.2.1.1, p.1.1.1.1, p.1.2, p.1.1.1.2), (p.1.1.2, p.2.2, p.2.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fix Alice's and Bob's shared state before their classical inputs are known. -/
def sharedState (n : ℕ) : DensityMatrix (SourceDim n * SourceDim n) :=
  (exactPhaseRoutingProcess (n := n) (fun _ _ ↦ false)).rhoLR

def prepareSource (n : ℕ) :=
  ofIsometry (schmidtProtocolInputIsometry (sourceWeights n))
    (schmidtProtocolInputIsometry_isometry (sourceWeights n)
      (sourceWeights_nonnegative n) (sourceWeights_sum n))

/-- The preparation appends exactly the fixed shared state to the input qubit. -/
theorem prepareSource_action (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (prepareSource n).action Q = oneRoundRoutingInputMatrix (sharedState n) Q := by
  rw [prepareSource, ofIsometry_action]
  exact (exactPhaseRoutingProcess_inputMatrix_eq (fun _ _ ↦ false) Q).symm

/-- Apply the two local channels in parallel, then send each message to the
other party. No operation before the exchange takes the other party's input. -/
def measuredRound (f : Address n → Address n → Bool) (x y : Address n) :=
  (FiniteKrausChannel.reindex (exchange n)).comp
    (((aliceSendChannel f x).tensor (bobSendChannel y)).comp (prepareSource n))

private def tagOrder (n : ℕ) :
    ((PhaseBob n × PhaseAlice n) × (Address n × Address n)) ≃
      (BobReceived n × AliceReceived n) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def sentFlags (p : PhaseBob n × PhaseAlice n) : Source n × Source n :=
  (p.1.1.2, p.2.2)

private def krausLabels (n : ℕ) :
    ((Fin 1 × ((Source n × Fin 1) × (Source n × Fin 1))) × Fin 1) ≃
      (Source n × Source n) where
  toFun k := (k.1.2.1.1, k.1.2.2.1)
  invFun k := ((0, (k.1, 0), (k.2, 0)), 0)
  left_inv := by
    rintro ⟨⟨a, ⟨r, b⟩, ⟨s, c⟩⟩, d⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    obtain rfl : c = 0 := Subsingleton.elim _ _
    obtain rfl : d = 0 := Subsingleton.elim _ _
    rfl
  right_inv _ := rfl

private theorem measuredRound_action (f : Address n → Address n → Bool)
    (x y : Address n) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (measuredRound f x y).action Q =
      ((FiniteKrausChannel.reindex (tagOrder n)).comp
        (recorded (phaseGlobal f x y) (phaseGlobal_isometry f x y) sentFlags (x, y))).action Q := by
  let indices := (Equiv.prodUnique (Source n × Source n) (Fin 1)).symm
  apply action_eq_of_kraus_equiv _ _ ((krausLabels n).trans indices)
  intro k
  ext p q
  rw [measuredRound, reindex_comp_kraus_apply, reindex_comp_kraus_apply, comp_kraus]
  rcases p with ⟨⟨⟨⟨d, h⟩, g'⟩, x'⟩, ⟨⟨a, g⟩, y'⟩⟩
  rcases k with ⟨⟨i, ⟨r, j⟩, ⟨s, l⟩⟩, m⟩
  simp only [Matrix.mul_apply, tensor_kraus, Matrix.kroneckerMap_apply, aliceSendChannel,
    bobSendChannel, reindex_comp_kraus_apply, aliceWireOrder, bobWireOrder, exchange,
    tagOrder, krausLabels, indices, Equiv.trans_apply, Equiv.prodUnique_symm_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, prepareSource, ofIsometry, recorded_kraus,
    recordedKraus, sentFlags, Prod.mk.injEq]
  have hcond : (x' = x ∧ y' = y) ∧ h = r ∧ g = s ↔
      (x' = x ∧ h = r) ∧ (y' = y ∧ g = s) := by tauto
  rw [if_congr hcond rfl rfl]
  by_cases ha : x' = x ∧ h = r <;> by_cases hb : y' = y ∧ g = s <;>
    simp [ha, hb, Matrix.mul_apply,
      phaseGlobal, schmidtProtocolGlobalIsometry, schmidtProtocolUnregroupedIsometry,
      schmidtProtocolLocalTensorIsometry, schmidtProtocolOutputRegroup]

private def bobFlags (b : PhaseBob n) : Source n × Source n := (b.1.2, b.2)
private def aliceFlags (a : PhaseAlice n) : Source n × Source n := (a.1.2, a.2)

private def coherentOutput (f : Address n → Address n → Bool) (x y : Address n)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (PhaseBob n × PhaseAlice n) (PhaseBob n × PhaseAlice n) ℂ :=
  phaseGlobal f x y * Q * (phaseGlobal f x y)ᴴ

/-- When either side has incompatible copies of a flag, that basis row has
zero amplitude. -/
private theorem coherentOutput_zero (f : Address n → Address n → Bool) (x y : Address n)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (b b' : PhaseBob n) (a a' : PhaseAlice n)
    (h : bobFlags b ≠ aliceFlags a ∨ bobFlags b' ≠ aliceFlags a') :
    coherentOutput f x y Q (b, a) (b', a') = 0 := by
  rcases h with h | h
  · have hz (q : Fin 2) := phaseGlobal_flags_match f x y b a q h
    simp [coherentOutput, Matrix.mul_apply, hz]
  · have hz (q : Fin 2) := phaseGlobal_flags_match f x y b' a' q h
    simp [coherentOutput, Matrix.mul_apply, Matrix.conjTranspose_apply, hz]

/-- The first round really dephases the two sent outcome records, and both
sent input labels are fixed in the computational basis. -/
theorem measuredRound_entry (f : Address n → Address n → Bool) (x y : Address n)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (b b' : BobReceived n) (a a' : AliceReceived n) :
    (measuredRound f x y).action Q (b, a) (b', a') =
      if (b.2, a.2) = (x, y) ∧ (b'.2, a'.2) = (x, y) ∧
          sentFlags (b.1, a.1) = sentFlags (b'.1, a'.1) then
        coherentOutput f x y Q (b.1, a.1) (b'.1, a'.1) else 0 := by
  rw [measuredRound_action, comp_action, reindex_action]
  exact recorded_action_apply _ _ _ _ _ _ _

private theorem aliceMarginal_entry (f : Address n → Address n → Bool) (x y : Address n)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (a a' : PhaseAlice n) (t : Address n) :
    firstFactorPartialTrace (BobReceived n) (AliceReceived n)
        ((measuredRound f x y).action Q) (a, t) (a', t) =
      if t = y then firstFactorPartialTrace (PhaseBob n) (PhaseAlice n)
          (coherentOutput f x y Q) a a' else 0 := by
  rw [firstFactorPartialTrace_apply, firstFactorPartialTrace_apply, Fintype.sum_prod_type]
  simp only [measuredRound_entry, Prod.mk.injEq, sentFlags]
  by_cases ht : t = y
  · subst t
    simp only [and_true, true_and, if_true]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hg : a.2 = a'.2
    · simp [hg]
    · have hz := coherentOutput_zero f x y Q b b a a' (by
        by_cases he : bobFlags b = aliceFlags a
        · exact Or.inr fun he' ↦ hg (congrArg (Prod.snd : Source n × Source n → Source n)
            (he.symm.trans he'))
        · exact Or.inl he)
      simp [hg, hz]
  · simp [ht]

private theorem bobMarginal_entry (f : Address n → Address n → Bool) (x y : Address n)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (b b' : PhaseBob n) (t : Address n) :
    environmentPartialTrace (BobReceived n) (AliceReceived n)
        ((measuredRound f x y).action Q) (b, t) (b', t) =
      if t = x then environmentPartialTrace (PhaseBob n) (PhaseAlice n)
          (coherentOutput f x y Q) b b' else 0 := by
  rw [environmentPartialTrace_apply, environmentPartialTrace_apply, Fintype.sum_prod_type]
  simp only [measuredRound_entry, Prod.mk.injEq, sentFlags]
  by_cases ht : t = x
  · subst t
    simp only [and_true, true_and, if_true]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hg : b.1.2 = b'.1.2
    · simp [hg]
    · have hz := coherentOutput_zero f x y Q b b' a a (by
        by_cases he : bobFlags b = aliceFlags a
        · exact Or.inr fun he' ↦ hg (congrArg Prod.fst (he.trans he'.symm))
        · exact Or.inl he)
      simp [hg, hz]
  · simp [ht]

/-- Alice reads Bob's input label from the received message. -/
def measuredAliceRecovery (f : Address n → Address n → Bool) (x : Address n) :=
  readTag (aliceRecovery (f x))

/-- Bob reads Alice's input label from the received message. -/
def measuredBobRecovery (f : Address n → Address n → Bool) (y : Address n) :=
  readTag (fun x ↦ bobRecovery (f x) y)

def aliceRecovered (f : Address n → Address n → Bool) (x y : Address n) :=
  (measuredAliceRecovery f x).comp ((discardFirst (BobReceived n) (AliceReceived n)).comp
    (measuredRound f x y))

def bobRecovered (f : Address n → Address n → Bool) (x y : Address n) :=
  (measuredBobRecovery f y).comp ((discardSecond (BobReceived n) (AliceReceived n)).comp
    (measuredRound f x y))

theorem aliceRecovered_exact (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = false) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (aliceRecovered f x y).action Q = Q := by
  rw [aliceRecovered, comp_action, comp_action, discardFirst_action, measuredAliceRecovery,
    readTag_action_fixed _ _ y _ (aliceMarginal_entry f x y Q)]
  simpa only [comp_action, discardFirst_action, schmidtProtocolGlobalChannel,
    ofIsometry_action, coherentOutput, phaseGlobal] using phaseAlice_exact f x y hf Q

theorem bobRecovered_exact (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = true) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (bobRecovered f x y).action Q = Q := by
  rw [bobRecovered, comp_action, comp_action, discardSecond_action, measuredBobRecovery,
    readTag_action_fixed _ _ x _ (bobMarginal_entry f x y Q)]
  simpa only [comp_action, discardSecond_action, schmidtProtocolGlobalChannel,
    ofIsometry_action, coherentOutput, phaseGlobal] using phaseBob_exact f x y hf Q

end

end LinearRouting.ExactPhase
