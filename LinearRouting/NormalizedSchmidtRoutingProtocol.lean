import LinearRouting.SchmidtProtocolGlobalChannel

/-!
# Exact Schmidt-form routing on finite carriers

The recovery fields require equality to the identity action on all qubit
matrices in the selected branch.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

universe uX uY

variable {X : Type uX} {Y : Type uY}

/-- Alice's complementary pre-recovery channel, obtained by discarding Bob's
two retained factors from the complete first-round isometry. -/
noncomputable def schmidtProtocolAliceReducedChannel
    {d n m a b : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Fin a × Fin n) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Fin m × Fin b) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    FiniteKrausChannel
      ((Fin 1) × (Fin n × Fin m)) (Fin 2) (Fin a × Fin b) :=
  (FiniteKrausChannel.discardFirst
      (Fin n × Fin m) (Fin a × Fin b)).comp
    (schmidtProtocolGlobalChannel lam hlam hlamSum
      Alice Bob hAlice hBob x y)

/-- Finite-indexed version of Alice's complementary pre-recovery channel. -/
noncomputable def schmidtProtocolAliceReducedFinChannel
    {d n m a b : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Fin a × Fin n) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Fin m × Fin b) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    FiniteKrausChannel
      ((((Fin 1) × (Fin n × Fin m)) × Fin 1))
      (Fin 2) (Fin (a * b)) :=
  (productReindexChannel a b).comp
    (schmidtProtocolAliceReducedChannel lam hlam hlamSum
      Alice Bob hAlice hBob x y)

universe uRA uRB

/-- A normalized one-round routing protocol in Schmidt form, on finite
carriers.  The output factors are ordered as follows:

* Bob's pre-recovery carrier is `Fin n × Fin m`, consisting of Alice's sent
  message and Bob's retained register;
* Alice's complementary carrier is `Fin a × Fin b`, consisting of Alice's
  retained register and Bob's sent message.

Each recovery field is exact on the input pairs assigned to that party. -/
structure NormalizedSchmidtRoutingProtocol
    (X : Type uX) (Y : Type uY) (RA : Type uRA) (RB : Type uRB)
    [Fintype RA] [Fintype RB]
    (d n m a b : ℕ) (f : X → Y → Bool) where
  lam : Fin d → ℝ
  lam_nonnegative : ∀ r, 0 ≤ lam r
  lam_sum : ∑ r, lam r = 1
  alice : X → Matrix (Fin a × Fin n) (Fin 2 × Fin d) ℂ
  bob : Y → Matrix (Fin m × Fin b) (Fin d) ℂ
  alice_isometry : ∀ x, (alice x)ᴴ * alice x = 1
  bob_isometry : ∀ y, (bob y)ᴴ * bob y = 1
  recoverAlice : X → Y →
    FiniteKrausChannel RA (Fin (a * b)) (Fin 2)
  recoverBob : X → Y →
    FiniteKrausChannel RB (Fin (n * m)) (Fin 2)
  alice_correct : ∀ x y, f x y = false → ∀ Q : Matrix (Fin 2) (Fin 2) ℂ,
    ((recoverAlice x y).comp
      (schmidtProtocolAliceReducedFinChannel
        lam lam_nonnegative lam_sum alice bob
        alice_isometry bob_isometry x y)).action Q = Q
  bob_correct : ∀ x y, f x y = true → ∀ Q : Matrix (Fin 2) (Fin 2) ℂ,
    ((recoverBob x y).comp
      (schmidtProtocolBobReducedFinChannel
        lam lam_nonnegative lam_sum alice bob
        alice_isometry bob_isometry x y)).action Q = Q

end LinearRouting
