import LinearRouting.ClassicalWire
import LinearRouting.Resource

/-!
# Linear entanglement suffices for f-routing

The paper's theorem is an existence result for a single protocol. Its
shared state, simultaneous exchange, local recoveries, and message widths
all refer to that protocol.
-/

namespace LinearRouting

open Matrix FiniteKrausChannel ExactPhase

set_option maxSynthPendingDepth 30
set_option synthInstance.maxSize 4096

noncomputable section

/-- A protocol on the wire types of the construction. The preparation
appends the pre-shared state. Each encoder and recovery receives only its
own party's input, together with the quantum and classical registers held
by that party at that stage. -/
structure OneRoundProtocol (n : ℕ) where
  resource : DensityMatrix (SourceDim n * SourceDim n)
  prepare : FiniteKrausChannel (Fin 1) (Fin 2) ((Fin 2 × Fin (SourceDim n)) × Fin (SourceDim n))
  prepare_action : ∀ Q, prepare.action Q = oneRoundRoutingInputMatrix resource Q
  aliceSend : Address n → FiniteKrausChannel (Source n × Fin 1)
    (Fin 2 × Fin (SourceDim n)) (AliceRetained n × AliceMessage n)
  bobSend : Address n → FiniteKrausChannel (Source n × Fin 1)
    (Fin (SourceDim n)) (BobRetained n × BobMessage n)
  aliceDecode : Address n → FiniteKrausChannel (Address n × (Fin 1 × AliceJunk n))
    (AliceReceived n) (Fin 2)
  bobDecode : Address n → FiniteKrausChannel (Address n × (Fin 1 × BobJunk n))
    (BobReceived n) (Fin 2)

namespace OneRoundProtocol

variable {n : ℕ}

/-- The only exchange sends each outgoing register to the other party. -/
def roundChannel (P : OneRoundProtocol n) (x y : Address n) :=
  (FiniteKrausChannel.reindex (exchange n)).comp
    (((P.aliceSend x).tensor (P.bobSend y)).comp P.prepare)

def recoveredByAlice (P : OneRoundProtocol n) (x y : Address n) :=
  (P.aliceDecode x).comp ((discardFirst (BobReceived n) (AliceReceived n)).comp
    (P.roundChannel x y))

def recoveredByBob (P : OneRoundProtocol n) (x y : Address n) :=
  (P.bobDecode y).comp ((discardSecond (BobReceived n) (AliceReceived n)).comp
    (P.roundChannel x y))

end OneRoundProtocol

/-- A qubit channel acts as the identity jointly with every finite reference. -/
def RecoversExactly {K : Type*} [Fintype K] (C : FiniteKrausChannel K (Fin 2) (Fin 2)) : Prop :=
  ∀ (r : ℕ) (Q : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ),
    (C.tensor (identity : FiniteKrausChannel (Fin 1) (Fin r) (Fin r))).action Q = Q

private theorem recoversExactly_of_action_eq {K : Type*} [Fintype K]
    (C : FiniteKrausChannel K (Fin 2) (Fin 2))
    (h : ∀ Q, C.action Q = Q) : RecoversExactly C := by
  intro r Q
  rw [tensor_identity_action_eq_of_action_eq C identity (fun M ↦ (h M).trans (identity_action M).symm)]
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [tensor_identity_action_apply, identity_action]

/-- The three properties in Theorem 1. The exact EPR equality uses the
computational basis of the two role/address blocks. The message widths
are basis equivalences, and the two dephasing fields certify that the
specified message components are classical. -/
structure RoutingGuarantees {n : ℕ} (f : Address n → Address n → Bool)
    (P : OneRoundProtocol n) : Prop where
  eprPairs : Matrix.reindex ((eprBasis n).prodCongr (eprBasis n))
      ((eprBasis n).prodCongr (eprBasis n)) (productMatrixOfReindexed P.resource.val) =
    eprPairsMatrix (2 * n + 2)
  aliceExact : ∀ x y, f x y = false → RecoversExactly (P.recoveredByAlice x y)
  bobExact : ∀ x y, f x y = true → RecoversExactly (P.recoveredByBob x y)
  aliceQuantumWires : Nonempty (AliceQuantumMessage n ≃ (Fin (2 ^ (n + 1) + 1) → ZMod 2))
  aliceClassicalWires : Nonempty (ClassicalMessage n ≃ (Fin (3 * n + 2) → ZMod 2))
  bobQuantumWires : Nonempty (BobQuantumMessage n ≃ (Fin 0 → ZMod 2))
  bobClassicalWires : Nonempty (BobMessage n ≃ (Fin (3 * n + 2) → ZMod 2))
  aliceClassical : ∀ x Q p p', p.2.2 ≠ p'.2.2 → (P.aliceSend x).action Q p p' = 0
  bobClassical : ∀ y Q p p', p.2 ≠ p'.2 → (P.bobSend y).action Q p p' = 0

/-- The measured phase protocol of the paper. -/
def phaseProtocol {n : ℕ} (f : Address n → Address n → Bool) : OneRoundProtocol n where
  resource := sharedState n
  prepare := prepareSource n
  prepare_action := prepareSource_action
  aliceSend := aliceSendChannel f
  bobSend := bobSendChannel
  aliceDecode := measuredAliceRecovery f
  bobDecode := measuredBobRecovery f

/-- The explicit protocol has the shared state, exact recoveries and
communication counts of Theorem 1. -/
theorem phaseProtocol_guarantees {n : ℕ} (f : Address n → Address n → Bool) :
    RoutingGuarantees f (phaseProtocol f) where
  eprPairs := exactPhaseRoutingProcess_resource_eq_eprPairs (fun _ _ ↦ false)
  aliceExact x y hf := recoversExactly_of_action_eq _ (aliceRecovered_exact f x y hf)
  bobExact x y hf := recoversExactly_of_action_eq _ (bobRecovered_exact f x y hf)
  aliceQuantumWires := ⟨aliceQuantumMessageBits n⟩
  aliceClassicalWires := ⟨classicalMessageBits n⟩
  bobQuantumWires := ⟨bobQuantumMessageBits n⟩
  bobClassicalWires := ⟨classicalMessageBits n⟩
  aliceClassical := aliceSendChannel_classical f
  bobClassical := bobSendChannel_classical

/-- Theorem 1 of the paper. Every Boolean function on two n-bit inputs
has a one-round protocol with (2n+2) shared EPR pairs and exact recovery.
Alice sends (2^{n+1}+1) qubits and (3n+2) classical bits. Bob's entire
message has (3n+2) classical bits. The construction also works at n = 0. -/
theorem linearEntanglement (n : ℕ) (f : Address n → Address n → Bool) :
    ∃ P : OneRoundProtocol n, RoutingGuarantees f P :=
  ⟨phaseProtocol f, phaseProtocol_guarantees f⟩

end

end LinearRouting
