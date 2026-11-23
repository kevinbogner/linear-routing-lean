import LinearRouting.FiniteKrausTensor
import LinearRouting.SchmidtProtocolGlobalChannel

/-!
# The local channels and wire swap of one-round routing

Each party's local channel depends only on its own input. The two local
channels act on the input and resource first. A permutation then places the
sent registers at their respective receivers.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

universe uX uY uKA uKB uKG uRA uRB

/-- Regroup the input qubit and the two resource factors from
`Q \otimes (L \otimes R)` to `(Q \otimes L) \otimes R`, the input ordering
expected by Alice's and Bob's local channels. -/
def oneRoundRoutingInputRegroup {l r : ℕ} :
    (Fin 2 × (Fin l × Fin r)) ≃ ((Fin 2 × Fin l) × Fin r) where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv p := by rcases p with ⟨q, i, j⟩; rfl
  right_inv p := by rcases p with ⟨⟨q, i⟩, j⟩; rfl

/-- Regroup the two local first-round outputs after the messages cross.
The first factor is Alice's final system `Akeep ⊗ BtoA`; the second is
Bob's final system `Bkeep ⊗ AtoB`. -/
def oneRoundRoutingOutputRegroup {aKeep aToB bKeep bToA : ℕ} :
    ((Fin aKeep × Fin aToB) × (Fin bKeep × Fin bToA)) ≃
      ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB)) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv p := by rcases p with ⟨⟨a, c⟩, b, d⟩; rfl
  right_inv p := by rcases p with ⟨⟨a, d⟩, b, c⟩; rfl

/-- The matrix `Q \otimes rhoLR`, explicitly regrouped so that Alice receives
the qubit and the left resource factor while Bob receives the right factor. -/
noncomputable def oneRoundRoutingInputMatrix {l r : ℕ}
    (rhoLR : DensityMatrix (l * r))
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin l) × Fin r) ((Fin 2 × Fin l) × Fin r) ℂ :=
  Matrix.reindex oneRoundRoutingInputRegroup oneRoundRoutingInputRegroup
    (Q ⊗ₖ productMatrixOfReindexed rhoLR.val)

/-- Apply the two local first-round channels to `Q \otimes rhoLR` and regroup
their outputs into Alice's and Bob's post-message systems. -/
noncomputable def oneRoundRoutingRealizedOutputMatrix
    {X : Type uX} {Y : Type uY}
    {KA : Type uKA} {KB : Type uKB} [Fintype KA] [Fintype KB]
    {l r aKeep aToB bKeep bToA : ℕ}
    (rhoLR : DensityMatrix (l * r))
    (alice : X → FiniteKrausChannel KA (Fin 2 × Fin l)
      (Fin aKeep × Fin aToB))
    (bob : Y → FiniteKrausChannel KB (Fin r)
      (Fin bKeep × Fin bToA))
    (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB))
      ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB)) ℂ :=
  Matrix.reindex oneRoundRoutingOutputRegroup oneRoundRoutingOutputRegroup
    (((alice x).tensor (bob y)).action
      (oneRoundRoutingInputMatrix rhoLR Q))

namespace FiniteKrausChannel

/-- Alice's pre-recovery channel, obtained from the global channel by
discarding Bob's final system and reindexing Alice's crossed product carrier
as `Fin (aKeep * bToA)`. -/
noncomputable def oneRoundRoutingAlicePreRecoveryChannel
    {X : Type uX} {Y : Type uY}
    {KG : Type uKG} [Fintype KG]
    {aKeep aToB bKeep bToA : ℕ}
    (global : X → Y → FiniteKrausChannel KG (Fin 2)
      ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB)))
    (x : X) (y : Y) :
    FiniteKrausChannel
      ((KG × (Fin bKeep × Fin aToB)) × Fin 1)
      (Fin 2) (Fin (aKeep * bToA)) :=
  (productReindexChannel aKeep bToA).comp
    ((discardSecond (Fin aKeep × Fin bToA)
      (Fin bKeep × Fin aToB)).comp (global x y))

/-- Bob's pre-recovery channel, obtained from the global channel by
discarding Alice's final system and reindexing Bob's crossed product carrier
as `Fin (bKeep * aToB)`. -/
noncomputable def oneRoundRoutingBobPreRecoveryChannel
    {X : Type uX} {Y : Type uY}
    {KG : Type uKG} [Fintype KG]
    {aKeep aToB bKeep bToA : ℕ}
    (global : X → Y → FiniteKrausChannel KG (Fin 2)
      ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB)))
    (x : X) (y : Y) :
    FiniteKrausChannel
      ((KG × (Fin aKeep × Fin bToA)) × Fin 1)
      (Fin 2) (Fin (bKeep * aToB)) :=
  (productReindexChannel bKeep aToB).comp
    ((discardFirst (Fin aKeep × Fin bToA)
      (Fin bKeep × Fin aToB)).comp (global x y))

end FiniteKrausChannel

end LinearRouting
