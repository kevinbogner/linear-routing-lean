# linear-routing-lean

Lean 4 formalization of the paper

> Kevin Bogner, *Linear entanglement suffices for f-routing*, [arXiv:2611.30947](https://arxiv.org/abs/2611.30947).

The paper shows that \(2n+2\) shared EPR pairs suffice for \(f\)-routing of
every Boolean function \(f\) on two \(n\)-bit inputs, at the price of an
exponentially long quantum message. This project proves Theorem 1 of the
paper and its Lemmas 2 and 3. The source tree is self-contained apart from
Mathlib, and the proofs use only Lean's three standard axioms.

## The statement to check

`Statement.lean`, at the top of the repository, states Theorem 1 as the
proposition
`LinearRouting.Statement.Theorem1`. The file imports only Mathlib, contains no
proof and has fewer than 200 lines. A reader who checks this one file knows
what the formalization proves, because Lean checks everything else.
`LinearRouting.theorem1` in `LinearRouting/StatementProof.lean` proves the
proposition.

The statement file follows Section 2 of the paper and defines \(f\)-routing
for arbitrary finite registers.

| In the paper | In `Statement.lean` |
| --- | --- |
| A quantum operation. | `Channel`, a family of Kraus matrices with the completeness relation |
| A strategy: the shared state and the operations of Alice and Bob. | `Strategy` |
| Each operation depends only on the input of its party. A recovery acts on the kept register and the received message. | The types of the four operations in `Strategy` |
| The qubit that the selected party ends with. | `Strategy.aliceRecovers`, `Strategy.bobRecovers` |
| \(2n+2\) EPR pairs. | `eprPairs (2 * n + 2)` |
| Classical bits in a message. | `Channel.ClassicalIn` |

`Theorem1` says that for every \(n\) and every Boolean function \(f\) there is
a strategy with the three properties of the theorem. Its shared state is
`eprPairs (2 * n + 2)`. The selected party recovers every matrix \(\rho\)
unchanged, so the map from the qubit to the recovered qubit is the identity
channel. Alice's message is a register of \(2^{n+1}+1\) qubits and \(3n+2\)
classical bits, and Bob's message is \(3n+2\) classical bits. The paper states
the theorem for \(n\ge 1\), and the Lean statement also covers \(n=0\).

## Theorem 1 on the registers of the construction

`LinearRouting.linearEntanglement` states the same theorem on the registers
that the construction uses, and `theorem1` follows from it by relabelling
these registers as bit strings. What the paper calls a strategy is a protocol
in this part of the code. The strategy of the paper is
`LinearRouting.phaseProtocol`, and `RoutingGuarantees` lists its properties.

| Property in the paper | Lean declaration |
| --- | --- |
| The shared state is the tensor product of \(2n+2\) EPR pairs, in the basis that labels each shared register by a bit and an address. | `RoutingGuarantees.eprPairs` |
| On every input pair, the selected party recovers the qubit perfectly. Its channel is the identity, also on a qubit that is entangled with any finite reference system. | `RoutingGuarantees.aliceExact`, `RoutingGuarantees.bobExact` |
| Alice sends \(2^{n+1}+1\) qubits and \(3n+2\) classical bits, and Bob sends \(3n+2\) classical bits. | `RoutingGuarantees.aliceQuantumWires`, `RoutingGuarantees.aliceClassicalWires`, `RoutingGuarantees.bobQuantumWires`, `RoutingGuarantees.bobClassicalWires` |
| Each party measures and writes its outcomes, together with its input string, into classical registers. | `ExactPhase.aliceSendChannel_entry`, `ExactPhase.bobSendChannel_entry` |

In the formal model, each operation before the exchange acts only on the
party's own input and its part of the shared state. The exchange routes the
outgoing registers to their receivers. Each recovery reads the other party's
input from the received message and acts on the registers that the party
holds. Bob's correction is controlled by the spectral projectors of the
observable on his work registers instead of following a measurement, which
gives the same channel, and the work registers are then discarded.

## Lemmas 2 and 3

| Result in the paper | Lean declaration |
| --- | --- |
| Lemma 2 (Commutation). The operators \(X_a\) and \(V_{x,a+y}\) anticommute when \(f(x,y)=0\) and commute when \(f(x,y)=1\). | `ExactPhase.commutation` |
| The phase operator of the circuit is the product of the Pauli \(Z\) operators selected by the shifted row of \(f\), as in the definition of \(V_{x,b}\). | `ExactPhase.workPhase_eq_pauliZ_product` |
| Lemma 3 (One block). For each pair of outcomes, the unnormalized state of one block has the stated sign and prefactor, and the work vector has norm one. | `ExactPhase.oneBlock` |
| The matrix in Lemma 3 has the form of \(M_z\) in the paper, and the work vector is \((M_z\otimes I)\lvert\Omega\rangle\). | `ExactPhase.outcomeMix_eq`, `ExactPhase.workPairAmplitude_eq_kronecker_mulVec` |

## Build and audit

With Elan installed, run the following commands in this folder. The Lean
toolchain and the Mathlib revision are pinned, both at v4.32.2.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the axioms behind `theorem1`, the numbered results and the
lemmas that connect their statements to the circuit. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

As the paper discloses, the formalization was written by GPT-6.2 Sol (OpenAI)
in a research session directed by the author, and Claude Fable 5.2 (Anthropic)
reviewed the formal statement. Claude Fable 5.2 later wrote the statement file
`Statement.lean` and its proof in `LinearRouting/StatementProof.lean`.
