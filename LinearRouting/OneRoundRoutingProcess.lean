import LinearRouting.OneRoundRoutingRealization

/-!
# Correctness-free one-round routing processes

This file separates the structural data of a raw one-round routing protocol
from its pointwise correctness assumptions.  A process contains the mixed
resource, the two input-indexed local channels, their exactly realized global
channel, and the two input-pair-indexed recovery channels.  Consequently the
same local operations can be run with no claim that either recovery branch is
correct.

The canonical constructor supplies the global channel and its realization
proof from arbitrary resource, local channels, and recoveries.
-/

namespace LinearRouting

open Matrix
open scoped ComplexOrder Kronecker

universe uX uY uKA uKB uKG uRA uRB

/-- The structural, correctness-free data of a finite-dimensional one-round
routing process. -/
structure OneRoundRoutingProcess
    (X : Type uX) (Y : Type uY)
    (KA : Type uKA) (KB : Type uKB) (KG : Type uKG)
    (RA : Type uRA) (RB : Type uRB)
    [Fintype KA] [Fintype KB] [Fintype KG]
    [Fintype RA] [Fintype RB]
    (l r aKeep aToB bKeep bToA : ℕ) where
  rhoLR : DensityMatrix (l * r)
  alice : X → FiniteKrausChannel KA (Fin 2 × Fin l)
    (Fin aKeep × Fin aToB)
  bob : Y → FiniteKrausChannel KB (Fin r)
    (Fin bKeep × Fin bToA)
  global : X → Y → FiniteKrausChannel KG (Fin 2)
    ((Fin aKeep × Fin bToA) × (Fin bKeep × Fin aToB))
  global_realization : ∀ x y Q,
    (global x y).action Q =
      oneRoundRoutingRealizedOutputMatrix rhoLR alice bob x y Q
  recoverAlice : X → Y →
    FiniteKrausChannel RA (Fin (aKeep * bToA)) (Fin 2)
  recoverBob : X → Y →
    FiniteKrausChannel RB (Fin (bKeep * aToB)) (Fin 2)

namespace OneRoundRoutingProcess

variable {X : Type uX} {Y : Type uY}
variable {KA : Type uKA} {KB : Type uKB} {KG : Type uKG}
variable {RA : Type uRA} {RB : Type uRB}
variable [Fintype KA] [Fintype KB] [Fintype KG]
variable [Fintype RA] [Fintype RB]
variable {l r aKeep aToB bKeep bToA : ℕ}

/-- Alice's reduced channel before recovery. -/
noncomputable def alicePreRecovery
    (P : OneRoundRoutingProcess X Y KA KB KG RA RB
      l r aKeep aToB bKeep bToA) (x : X) (y : Y) :=
  FiniteKrausChannel.oneRoundRoutingAlicePreRecoveryChannel P.global x y

/-- Bob's reduced channel before recovery. -/
noncomputable def bobPreRecovery
    (P : OneRoundRoutingProcess X Y KA KB KG RA RB
      l r aKeep aToB bKeep bToA) (x : X) (y : Y) :=
  FiniteKrausChannel.oneRoundRoutingBobPreRecoveryChannel P.global x y

/-- Alice's reduced channel acts as the partial trace of the exact realized
first-round output. -/
theorem alicePreRecovery_action
    (P : OneRoundRoutingProcess X Y KA KB KG RA RB
      l r aKeep aToB bKeep bToA)
    (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (P.alicePreRecovery x y).action Q =
      reindexProductMatrix
        (environmentPartialTrace
          (Fin aKeep × Fin bToA) (Fin bKeep × Fin aToB)
          (oneRoundRoutingRealizedOutputMatrix
            P.rhoLR P.alice P.bob x y Q)) := by
  rw [alicePreRecovery,
    FiniteKrausChannel.oneRoundRoutingAlicePreRecoveryChannel,
    FiniteKrausChannel.comp_action,
    productReindexChannel_action,
    FiniteKrausChannel.comp_action,
    FiniteKrausChannel.discardSecond_action,
    P.global_realization]

/-- Bob's reduced channel acts as the partial trace of the exact realized
first-round output. -/
theorem bobPreRecovery_action
    (P : OneRoundRoutingProcess X Y KA KB KG RA RB
      l r aKeep aToB bKeep bToA)
    (x : X) (y : Y) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (P.bobPreRecovery x y).action Q =
      reindexProductMatrix
        (firstFactorPartialTrace
          (Fin aKeep × Fin bToA) (Fin bKeep × Fin aToB)
          (oneRoundRoutingRealizedOutputMatrix
            P.rhoLR P.alice P.bob x y Q)) := by
  rw [bobPreRecovery,
    FiniteKrausChannel.oneRoundRoutingBobPreRecoveryChannel,
    FiniteKrausChannel.comp_action,
    productReindexChannel_action,
    FiniteKrausChannel.comp_action,
    FiniteKrausChannel.discardFirst_action,
    P.global_realization]

/-- Build a correctness-free process from arbitrary resource, local channels,
and recovery channels.  The global channel is the canonical exact
realization. -/
noncomputable def ofCanonicalGlobal
    (rhoLR : DensityMatrix (l * r))
    (alice : X → FiniteKrausChannel KA (Fin 2 × Fin l)
      (Fin aKeep × Fin aToB))
    (bob : Y → FiniteKrausChannel KB (Fin r)
      (Fin bKeep × Fin bToA))
    (recoverAlice : X → Y →
      FiniteKrausChannel RA (Fin (aKeep * bToA)) (Fin 2))
    (recoverBob : X → Y →
      FiniteKrausChannel RB (Fin (bKeep * aToB)) (Fin 2)) :
    OneRoundRoutingProcess X Y KA KB
      (OneRoundRoutingCanonicalGlobalKraus KA KB l r) RA RB
      l r aKeep aToB bKeep bToA where
  rhoLR := rhoLR
  alice := alice
  bob := bob
  global := oneRoundRoutingCanonicalGlobalChannel rhoLR alice bob
  global_realization :=
    oneRoundRoutingCanonicalGlobalChannel_action rhoLR alice bob
  recoverAlice := recoverAlice
  recoverBob := recoverBob

end OneRoundRoutingProcess

end LinearRouting
