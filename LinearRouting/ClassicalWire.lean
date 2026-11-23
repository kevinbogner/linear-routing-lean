import LinearRouting.Protocol

/-!
# The outgoing classical registers

Both local encoders write their input into the outgoing message and
dephase the measured outcomes. The resulting matrices are block diagonal
in the classical portion of each message for any local input matrix.
-/

namespace LinearRouting.ExactPhase

open Matrix FiniteKrausChannel

set_option maxSynthPendingDepth 30
set_option synthInstance.maxSize 4096

variable {n : ℕ}

/-- Alice's input label is fixed and off-diagonal entries between distinct
outcome labels vanish. -/
theorem aliceSendChannel_entry (f : Address n → Address n → Bool) (x : Address n)
    (Q : Matrix (Fin 2 × Fin (SourceDim n)) (Fin 2 × Fin (SourceDim n)) ℂ)
    (p p' : AliceRetained n × AliceMessage n) :
    (aliceSendChannel f x).action Q p p' =
      if p.2.2.1 = x ∧ p'.2.2.1 = x ∧ p.2.2.2 = p'.2.2.2 then
        (phaseAlice f x * Q * (phaseAlice f x)ᴴ)
          (p.1, p.2.1, p.2.2.2) (p'.1, p'.2.1, p'.2.2.2)
      else 0 := by
  rw [aliceSendChannel, comp_action, reindex_action]
  exact recorded_action_apply _ _ _ _ _ _ _

/-- Bob's input label is fixed and off-diagonal entries between distinct
outcome labels vanish. -/
theorem bobSendChannel_entry (y : Address n)
    (Q : Matrix (Fin (SourceDim n)) (Fin (SourceDim n)) ℂ)
    (p p' : BobRetained n × BobMessage n) :
    (bobSendChannel y).action Q p p' =
      if p.2.1 = y ∧ p'.2.1 = y ∧ p.2.2 = p'.2.2 then
        (phaseBob y * Q * (phaseBob y)ᴴ) (p.1, p.2.2) (p'.1, p'.2.2)
      else 0 := by
  rw [bobSendChannel, comp_action, reindex_action]
  exact recorded_action_apply _ _ _ _ _ _ _

/-- Alice's message is block diagonal in its classical component. -/
theorem aliceSendChannel_classical (f : Address n → Address n → Bool) (x : Address n)
    (Q : Matrix (Fin 2 × Fin (SourceDim n)) (Fin 2 × Fin (SourceDim n)) ℂ)
    (p p' : AliceRetained n × AliceMessage n) (h : p.2.2 ≠ p'.2.2) :
    (aliceSendChannel f x).action Q p p' = 0 := by
  rw [aliceSendChannel_entry, if_neg]
  rintro ⟨hx, hx', hflags⟩
  exact h (Prod.ext (hx.trans hx'.symm) hflags)

/-- Bob's entire message is block diagonal. -/
theorem bobSendChannel_classical (y : Address n)
    (Q : Matrix (Fin (SourceDim n)) (Fin (SourceDim n)) ℂ)
    (p p' : BobRetained n × BobMessage n) (h : p.2 ≠ p'.2) :
    (bobSendChannel y).action Q p p' = 0 := by
  rw [bobSendChannel_entry, if_neg]
  rintro ⟨hy, hy', hflags⟩
  exact h (Prod.ext (hy.trans hy'.symm) hflags)

end LinearRouting.ExactPhase
