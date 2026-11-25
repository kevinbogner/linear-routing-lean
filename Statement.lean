import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The statement of Theorem 1

This file states Theorem 1 of the paper *Linear entanglement suffices for
f-routing* and nothing else. It imports only Mathlib and contains no proof.
A reader who checks this file knows what the formalization proves. The proof
is in `LinearRouting/StatementProof.lean`.

The file follows Section 2 of the paper. A strategy consists of a shared
state and four operations. Alice and Bob apply their operations, exchange
one message each, and the selected party recovers the qubit.
-/

namespace LinearRouting.Statement

open Matrix
open scoped Kronecker ComplexOrder

/-! ## Registers, operations and EPR pairs -/

/-- The two basis states of a qubit. -/
abbrev Qubit := Fin 2

/-- Strings of `m` bits. They are the inputs of Alice and Bob for `m = n`, and
they label the basis states of a register of `m` qubits. -/
abbrev Bits (m : ℕ) := Fin m → Fin 2

/-- A quantum operation from a register with basis `I` to a register with
basis `O`, given by its Kraus matrices. Every quantum operation has this form,
including a measurement that writes its outcome into a register. -/
structure Channel (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] where
  /-- The labels of the Kraus matrices. -/
  Index : Type
  [fintypeIndex : Fintype Index]
  /-- The Kraus matrices, with rows indexed by `O` and columns by `I`. -/
  kraus : Index → Matrix O I ℂ
  /-- The completeness relation, which makes the operation trace preserving. -/
  complete : ∑ k, (kraus k)ᴴ * kraus k = 1

attribute [instance] Channel.fintypeIndex

section Operations

variable {I O J P : Type} [Fintype I] [DecidableEq I] [Fintype O]
  [Fintype J] [DecidableEq J] [Fintype P]

/-- The operation `C` applied to the matrix `ρ`. -/
def Channel.apply (C : Channel I O) (ρ : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ k, C.kraus k * ρ * (C.kraus k)ᴴ

/-- The operations `C` and `D` applied side by side to a joint state of two
registers. The matrix `A ⊗ₖ B` has the entries `A i i' * B j j'`. -/
def Channel.both (C : Channel I O) (D : Channel J P)
    (ρ : Matrix (I × J) (I × J) ℂ) : Matrix (O × P) (O × P) ℂ :=
  ∑ k, ∑ l, (C.kraus k ⊗ₖ D.kraus l) * ρ * (C.kraus k ⊗ₖ D.kraus l)ᴴ

/-- The part `part o` of the output register is classical: whatever the
input, the output has no entry between two different values of that part. -/
def Channel.ClassicalIn {B : Type} (C : Channel I O) (part : O → B) : Prop :=
  ∀ (ρ : Matrix I I ℂ) (p q : O), part p ≠ part q → C.apply ρ p q = 0

end Operations

/-- The density matrix of one EPR pair `(|00⟩ + |11⟩)/√2`. -/
noncomputable def eprPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q ↦ if p.1 = p.2 ∧ q.1 = q.2 then 1 / 2 else 0

/-- The density matrix of `m` EPR pairs. Alice holds the first qubit of every
pair and Bob the second. An entry of a tensor product is the product of the
entries of its factors. -/
noncomputable def eprPairs (m : ℕ) : Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ :=
  fun p q ↦ ∏ i, eprPair (p.1 i, p.2 i) (q.1 i, q.2 i)

/-! ## Strategies -/

section Strategies

variable (n : ℕ) (L R AK AM BK BM : Type)
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype AK] [DecidableEq AK] [Fintype AM] [DecidableEq AM]
  [Fintype BK] [DecidableEq BK] [Fintype BM] [DecidableEq BM]

/-- A strategy for routing with inputs of `n` bits. Alice holds the part `L`
of the shared state and Bob the part `R`. Alice keeps the register `AK` and
sends `AM`. Bob keeps `BK` and sends `BM`. Every operation depends only on
the input of the party that applies it. -/
structure Strategy where
  /-- The shared state, a density matrix. -/
  shared : Matrix (L × R) (L × R) ℂ
  shared_posSemidef : shared.PosSemidef
  shared_trace : shared.trace = 1
  /-- Alice's operation on the qubit and her part of the shared state. -/
  aliceOperation : Bits n → Channel (Qubit × L) (AK × AM)
  /-- Bob's operation on his part of the shared state. -/
  bobOperation : Bits n → Channel R (BK × BM)
  /-- Alice's recovery, applied to her kept register and Bob's message. -/
  aliceRecovery : Bits n → Channel (AK × BM) Qubit
  /-- Bob's recovery, applied to his kept register and Alice's message. -/
  bobRecovery : Bits n → Channel (BK × AM) Qubit

variable {n L R AK AM BK BM}
variable (S : Strategy n L R AK AM BK BM)

/-- The qubit in the state `ρ` next to the shared state. Alice holds the qubit
and `L`, and Bob holds `R`. -/
def Strategy.start (ρ : Matrix Qubit Qubit ℂ) :
    Matrix ((Qubit × L) × R) ((Qubit × L) × R) ℂ :=
  fun p q ↦ ρ p.1.1 q.1.1 * S.shared (p.1.2, p.2) (q.1.2, q.2)

/-- The state after both operations and before the exchange. Alice holds
`AK × AM` and Bob holds `BK × BM`. -/
def Strategy.beforeExchange (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix ((AK × AM) × (BK × BM)) ((AK × AM) × (BK × BM)) ℂ :=
  (S.aliceOperation x).both (S.bobOperation y) (S.start ρ)

/-- Alice's state after the exchange: her kept register and Bob's message.
The sum traces out the two registers that Bob holds. -/
def Strategy.aliceHolds (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix (AK × BM) (AK × BM) ℂ :=
  fun p q ↦ ∑ m : AM, ∑ k : BK,
    S.beforeExchange x y ρ ((p.1, m), (k, p.2)) ((q.1, m), (k, q.2))

/-- Bob's state after the exchange: his kept register and Alice's message.
The sum traces out the two registers that Alice holds. -/
def Strategy.bobHolds (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix (BK × AM) (BK × AM) ℂ :=
  fun p q ↦ ∑ k : AK, ∑ m : BM,
    S.beforeExchange x y ρ ((k, p.2), (p.1, m)) ((k, q.2), (q.1, m))

/-- The qubit that Alice recovers when the qubit started in the state `ρ`. -/
def Strategy.aliceRecovers (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  (S.aliceRecovery x).apply (S.aliceHolds x y ρ)

/-- The qubit that Bob recovers when the qubit started in the state `ρ`. -/
def Strategy.bobRecovers (x y : Bits n) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  (S.bobRecovery y).apply (S.bobHolds x y ρ)

end Strategies

/-! ## Theorem 1 -/

/-- Theorem 1 of the paper. For every `n` and every Boolean function `f` on
two `n`-bit inputs there is a strategy with the following three properties.

1. The shared state is `2n+2` EPR pairs.
2. On every input pair `(x, y)`, the selected party recovers the qubit
   perfectly: Alice if `f x y = 0`, and Bob if `f x y = 1`. The recovered
   matrix equals `ρ` for every matrix `ρ`. Both sides are linear in `ρ`, so
   the map from the qubit to the recovered qubit is the identity channel, and
   a qubit that is entangled with another system is recovered together with
   its entanglement.
3. Alice sends `2^(n+1)+1` qubits and `3n+2` classical bits, and Bob sends
   `3n+2` classical bits.

The kept registers have some finite dimensions `a` and `b`. The paper states
the theorem for `n ≥ 1`. The statement here also covers `n = 0`. -/
def Theorem1 : Prop :=
  ∀ (n : ℕ) (f : Bits n → Bits n → Fin 2),
    ∃ (a b : ℕ)
      (S : Strategy n (Bits (2 * n + 2)) (Bits (2 * n + 2))
        (Fin a) (Bits (2 ^ (n + 1) + 1) × Bits (3 * n + 2))
        (Fin b) (Bits (3 * n + 2))),
      S.shared = eprPairs (2 * n + 2) ∧
      (∀ x y, f x y = 0 → ∀ ρ, S.aliceRecovers x y ρ = ρ) ∧
      (∀ x y, f x y = 1 → ∀ ρ, S.bobRecovers x y ρ = ρ) ∧
      (∀ x, (S.aliceOperation x).ClassicalIn fun o ↦ o.2.2) ∧
      (∀ y, (S.bobOperation y).ClassicalIn fun o ↦ o.2)

end LinearRouting.Statement
