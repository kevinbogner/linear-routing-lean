import LinearRouting.FiniteKrausCorrectnessTransport
import LinearRouting.ExactPhaseCircuit
import LinearRouting.ExactPhaseAliceDecode
import LinearRouting.ExactPhaseBobDecode
import LinearRouting.ExactPhaseFlagDecode
import LinearRouting.ExactPhaseChannel
import LinearRouting.ExactPhaseRawBridge
import LinearRouting.ExactPhaseSchmidtBridge

/-!
# Exact recovery for the phase router

Alice reverses the work preparations and the Bell transform on a zero
input. Bob reads the two work eigenspaces and removes the Pauli pad on a
one input. In both cases the unwanted registers factor out of the
recovered qubit.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators

set_option maxSynthPendingDepth 30
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

noncomputable section

variable {n : ℕ}

abbrev PhaseFlags (n : ℕ) := Source n × Source n
abbrev AliceAux (n : ℕ) := Fin 2 × Pair (Work n)
abbrev BobAux (n : ℕ) := Pair (Work n)
abbrev AliceJunk (n : ℕ) := AliceAux n × PhaseFlags n
abbrev BobJunk (n : ℕ) := BobAux n × PhaseFlags n

private def aliceBranch (row : Address n → Bool) (y : Address n) (g : PhaseFlags n) :
    Matrix (Fin 2 × AliceAux n) (AliceData (Work n)) ℂ :=
  fun p k ↦
    (if row y = false then
      aliceDecode (outcomeMix row y g.1.1 g.2.1) (outcomeMix row y g.1.2 g.2.2)
    else aliceDecode (fun _ ↦ 1) (fun _ ↦ 1)) ((p.1, p.2.1), p.2.2) k

private theorem aliceBranch_isometry (row : Address n → Bool) (y : Address n)
    (g : PhaseFlags n) : (aliceBranch row y g)ᴴ * aliceBranch row y g = 1 := by
  let D : Matrix ((Fin 2 × Fin 2) × Pair (Work n)) (AliceData (Work n)) ℂ :=
    if row y = false then
      aliceDecode (outcomeMix row y g.1.1 g.2.1) (outcomeMix row y g.1.2 g.2.2)
    else aliceDecode (fun _ ↦ 1) (fun _ ↦ 1)
  have hD : Dᴴ * D = 1 := by
    by_cases hf : row y = false
    · dsimp only [D]
      rw [if_pos hf]
      exact aliceDecode_isometry _ _
        (fun z ↦ outcomeMix_false_isometry row y g.1.1 g.2.1 z hf)
        (fun z ↦ outcomeMix_false_isometry row y g.1.2 g.2.2 z hf)
    · dsimp only [D]
      rw [if_neg hf]
      exact aliceDecode_isometry
        (fun _ ↦ (1 : Matrix (Work n) (Work n) ℂ)) (fun _ ↦ 1)
        (fun _ ↦ by simp) (fun _ ↦ by simp)
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, aliceBranch]
  change (∑ p : Fin 2 × AliceAux n, star (D ((p.1, p.2.1), p.2.2) i) *
    D ((p.1, p.2.1), p.2.2) j) = _
  calc
    _ = ∑ p, star (D p i) * D p j :=
      Equiv.sum_comp (Equiv.prodAssoc (Fin 2) (Fin 2) (Pair (Work n))).symm
        (fun p ↦ star (D p i) * D p j)
    _ = _ := congr_fun₂ hD i j

private def bobBranch (row : Address n → Bool) (y : Address n) (g : PhaseFlags n) :
    Matrix (Fin 2 × BobAux n) (BobData (Work n)) ℂ :=
  if row y = true then
    bobCorrection (outcomeProjector row y g.1.1 g.2.1) (outcomeProjector row y g.1.2 g.2.2)
  else 1

private theorem bobBranch_isometry (row : Address n → Bool) (y : Address n)
    (g : PhaseFlags n) : (bobBranch row y g)ᴴ * bobBranch row y g = 1 := by
  by_cases hf : row y = true
  · simp only [bobBranch, hf, if_true]
    exact bobCorrection_conjTranspose_mul _ _
      (fun z ↦ outcomeProjector_conjTranspose row y g.1.1 g.2.1 z hf)
      (fun z ↦ outcomeProjector_conjTranspose row y g.1.2 g.2.2 z hf)
      (fun z w ↦ outcomeProjector_mul row y g.1.1 g.2.1 z w hf)
      (fun z w ↦ outcomeProjector_mul row y g.1.2 g.2.2 z w hf)
      (outcomeProjector_sum _ _ _ _) (outcomeProjector_sum _ _ _ _)
  · simp [bobBranch, hf]

def aliceRecoveryMatrix (row : Address n → Bool) (y : Address n) :
    Matrix (Fin 2 × AliceJunk n) (PhaseAlice n) ℂ :=
  flagDecode (aliceBranch row y)

def bobRecoveryMatrix (row : Address n → Bool) (y : Address n) :
    Matrix (Fin 2 × BobJunk n) (PhaseBob n) ℂ :=
  flagDecode (bobBranch row y)

theorem aliceRecoveryMatrix_isometry (row : Address n → Bool) (y : Address n) :
    (aliceRecoveryMatrix row y)ᴴ * aliceRecoveryMatrix row y = 1 :=
  flagDecode_isometry _ (aliceBranch_isometry row y)

theorem bobRecoveryMatrix_isometry (row : Address n → Bool) (y : Address n) :
    (bobRecoveryMatrix row y)ᴴ * bobRecoveryMatrix row y = 1 :=
  flagDecode_isometry _ (bobBranch_isometry row y)

private def aliceResidual (j : AliceJunk n) (b : PhaseBob n) : ℂ :=
  if j.2.1 = b.1.2 ∧ b.2 = j.2.2 then
    globalScale b.1.2 b.2 *
      (if j.1.1 = b.1.1.1 ∧ j.1.2.1 = b.1.1.2.1 ∧ j.1.2.2 = b.1.1.2.2
        then invSqrtTwo else 0)
  else 0

private def bobResidual (row : Address n → Bool) (y : Address n)
    (j : BobJunk n) (a : PhaseAlice n) : ℂ :=
  if a.1.2 = j.2.1 ∧ j.2.2 = a.2 then
    globalScale j.2.1 j.2.2 * (2 : ℂ)⁻¹ *
      outcomeMix row y j.2.1.1 j.2.2.1 a.1.1.1.1 j.1.1 a.1.1.2.1 *
      outcomeMix row y j.2.1.2 j.2.2.2 a.1.1.1.2 j.1.2 a.1.1.2.2
  else 0

private theorem aliceFactor (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = false) (out : Fin 2) (j : AliceJunk n) (b : PhaseBob n) (q : Fin 2) :
    (∑ a, aliceRecoveryMatrix (f x) y (out, j) a * phaseGlobal f x y (b, a) q) =
      if out = q then aliceResidual j b else 0 := by
  rcases j with ⟨⟨anc, p'₁, p'₂⟩, h', g'⟩
  rcases b with ⟨⟨⟨c, p₁, p₂⟩, h⟩, g⟩
  rw [aliceRecoveryMatrix, flagDecode_contract]
  by_cases hh : h' = h ∧ g = g'
  · obtain ⟨he, ge⟩ := hh
    subst h'
    subst g'
    let O₁ := outcomeMix (f x) y h.1 g.1
    let O₂ := outcomeMix (f x) y h.2 g.2
    calc
      _ = globalScale h g * (∑ k : AliceData (Work n),
          aliceDecode O₁ O₂ ((out, anc), p'₁, p'₂) k *
            ((2 : ℂ)⁻¹ * pauli k.1 c q *
              O₁ k.1.1 p₁ k.2.1 * O₂ k.1.2 p₂ k.2.2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro _ _
        rw [phaseGlobal_apply]
        simp only [and_self, if_true, aliceBranch, if_pos hf]
        dsimp only [O₁, O₂]
        ring
      _ = _ := by
        rw [aliceDecode_amplitude _ _
          (fun z ↦ outcomeMix_false_mul_transpose (f x) y h.1 g.1 z hf)
          (fun z ↦ outcomeMix_false_mul_transpose (f x) y h.2 g.2 z hf)]
        by_cases hq : out = q <;> simp [hq, aliceResidual]
  · simp only [aliceResidual, hh, if_false, ite_self]
    apply Finset.sum_eq_zero
    intro _ _
    rw [phaseGlobal_apply, if_neg hh, mul_zero]

private theorem bobFactor (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = true) (out : Fin 2) (j : BobJunk n) (a : PhaseAlice n) (q : Fin 2) :
    (∑ b, bobRecoveryMatrix (f x) y (out, j) b * phaseGlobal f x y (b, a) q) =
      if out = q then bobResidual (f x) y j a else 0 := by
  rcases j with ⟨⟨p₁, p₂⟩, h, g⟩
  rcases a with ⟨⟨⟨k, p'₁, p'₂⟩, h'⟩, g'⟩
  rw [bobRecoveryMatrix, flagDecode_contract]
  by_cases hh : h' = h ∧ g = g'
  · obtain ⟨he, ge⟩ := hh
    subst h'
    subst g'
    let O₁ := outcomeMix (f x) y h.1 g.1
    let O₂ := outcomeMix (f x) y h.2 g.2
    let E₁ := outcomeProjector (f x) y h.1 g.1
    let E₂ := outcomeProjector (f x) y h.2 g.2
    calc
      _ = (globalScale h g * (2 : ℂ)⁻¹) * (∑ b : BobData (Work n),
          bobCorrection E₁ E₂ (out, p₁, p₂) b *
            (pauli k b.1 q * O₁ k.1 b.2.1 p'₁ * O₂ k.2 b.2.2 p'₂)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro _ _
        rw [phaseGlobal_apply]
        simp only [and_self, if_true, bobBranch, if_pos hf]
        dsimp only [O₁, O₂, E₁, E₂]
        ring
      _ = _ := by
        rw [bobCorrection_decode_amplitude _ _ _ _
          (fun k z ↦ outcomeProjector_mul_outcomeMix (f x) y h.1 g.1 k z hf)
          (fun k z ↦ outcomeProjector_mul_outcomeMix (f x) y h.2 g.2 k z hf)]
        by_cases hq : out = q <;> simp [hq, bobResidual, mul_assoc]
  · simp only [bobResidual, hh, if_false, ite_self]
    apply Finset.sum_eq_zero
    intro _ _
    rw [phaseGlobal_apply, if_neg hh, mul_zero]

def aliceRecovery (row : Address n → Bool) (y : Address n) :
    FiniteKrausChannel (Fin 1 × AliceJunk n) (PhaseAlice n) (Fin 2) :=
  (FiniteKrausChannel.discardSecond (Fin 2) (AliceJunk n)).comp
    (FiniteKrausChannel.ofIsometry (aliceRecoveryMatrix row y)
      (aliceRecoveryMatrix_isometry row y))

def bobRecovery (row : Address n → Bool) (y : Address n) :
    FiniteKrausChannel (Fin 1 × BobJunk n) (PhaseBob n) (Fin 2) :=
  (FiniteKrausChannel.discardSecond (Fin 2) (BobJunk n)).comp
    (FiniteKrausChannel.ofIsometry (bobRecoveryMatrix row y)
      (bobRecoveryMatrix_isometry row y))

theorem phaseAlice_exact (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = false) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((aliceRecovery (f x) y).comp
      ((FiniteKrausChannel.discardFirst (PhaseBob n) (PhaseAlice n)).comp
        (schmidtProtocolGlobalChannel (sourceWeights n)
          (sourceWeights_nonnegative n) (sourceWeights_sum n)
          (phaseAlice f) phaseBob (phaseAlice_isometry f) phaseBob_isometry x y))).action Q = Q :=
  decodeSecond_action_eq (phaseGlobal f x y) (aliceRecoveryMatrix (f x) y)
    (phaseGlobal_isometry f x y) (aliceRecoveryMatrix_isometry (f x) y)
    aliceResidual (aliceFactor f x y hf) Q

theorem phaseBob_exact (f : Address n → Address n → Bool) (x y : Address n)
    (hf : f x y = true) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ((bobRecovery (f x) y).comp
      ((FiniteKrausChannel.discardSecond (PhaseBob n) (PhaseAlice n)).comp
        (schmidtProtocolGlobalChannel (sourceWeights n)
          (sourceWeights_nonnegative n) (sourceWeights_sum n)
          (phaseAlice f) phaseBob (phaseAlice_isometry f) phaseBob_isometry x y))).action Q = Q :=
  decodeFirst_action_eq (phaseGlobal f x y) (bobRecoveryMatrix (f x) y)
    (phaseGlobal_isometry f x y) (bobRecoveryMatrix_isometry (f x) y)
    (bobResidual (f x) y) (bobFactor f x y hf) Q

/-- Every binary predicate has an exact one-round router. Its source is
maximally entangled with local dimension \(2^{2n+2}\). -/
def exactPhaseRouter (f : Address n → Address n → Bool) :
    ProductSchmidtExactRouter (Address n) (Address n)
      (AliceKeep (Label n) (Work n)) (AliceSend (Label n) (Work n)) (Source n) (Source n)
      (Fin 1 × AliceJunk n) (Fin 1 × BobJunk n) (SourceDim n) f where
  lam := sourceWeights n
  lam_nonnegative := sourceWeights_nonnegative n
  lam_sum := sourceWeights_sum n
  alice := phaseAlice f
  bob := phaseBob
  alice_isometry := phaseAlice_isometry f
  bob_isometry := phaseBob_isometry
  recoverAlice x y := aliceRecovery (f x) y
  recoverBob x y := bobRecovery (f x) y
  alice_exact := phaseAlice_exact f
  bob_exact := phaseBob_exact f

/-- The same construction in the repository's normalized routing model. -/
def exactPhaseRouterNormalized (f : Address n → Address n → Bool) :=
  (exactPhaseRouter f).toNormalized

/-- Every Schmidt weight equals \(2^{-(2n+2)}\), the weight of a basis
string of \(2n+2\) shared EPR pairs. -/
theorem exactPhaseRouterNormalized_weight (f : Address n → Address n → Bool)
    (j : Fin (2 ^ (2 * n + 2))) :
    (exactPhaseRouterNormalized f).lam j = ((2 ^ (2 * n + 2) : ℕ) : ℝ)⁻¹ := rfl

/-- The one-round phase construction on the raw resource and local channels. -/
def exactPhaseRoutingProcess (f : Address n → Address n → Bool) :=
  SchmidtRaw.toProcess (exactPhaseRouterNormalized f)

/-- The resource of the raw process induces the source embedding used by the
product-indexed circuit. -/
theorem exactPhaseRoutingProcess_inputMatrix_eq (f : Address n → Address n → Bool)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    oneRoundRoutingInputMatrix (exactPhaseRoutingProcess f).rhoLR Q =
      schmidtProtocolInputIsometry (sourceWeights n) * Q *
        (schmidtProtocolInputIsometry (sourceWeights n))ᴴ :=
  SchmidtRaw.inputMatrix_eq (exactPhaseRouterNormalized f) Q

/-- On a zero input the recovered channel at Alice is the identity. -/
theorem exactPhaseRoutingProcess_alice (f : Address n → Address n → Bool)
    (x y : Address n) (hf : f x y = false) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (((exactPhaseRoutingProcess f).recoverAlice x y).comp
      ((exactPhaseRoutingProcess f).alicePreRecovery x y)).action Q = Q := by
  unfold exactPhaseRoutingProcess
  rw [SchmidtRaw.aliceRecovered_action_eq]
  exact (exactPhaseRouter f).toNormalized_alice_exact x y hf Q

/-- On a one input the recovered channel at Bob is the identity. -/
theorem exactPhaseRoutingProcess_bob (f : Address n → Address n → Bool)
    (x y : Address n) (hf : f x y = true) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (((exactPhaseRoutingProcess f).recoverBob x y).comp
      ((exactPhaseRoutingProcess f).bobPreRecovery x y)).action Q = Q := by
  unfold exactPhaseRoutingProcess
  rw [SchmidtRaw.bobRecovered_action_eq]
  exact (exactPhaseRouter f).toNormalized_bob_exact x y hf Q

private theorem identity_zeroError :
    FiniteKrausChannel.FullDiamondErrorAtMost
      (FiniteKrausChannel.identity : FiniteKrausChannel (Fin 1) (Fin 2) (Fin 2))
      FiniteKrausChannel.identity 0 := by
  constructor <;> intros <;>
    simp

/-- Alice's exactness includes inputs entangled with an arbitrary finite reference. -/
theorem exactPhaseRoutingProcess_alice_zeroError
    (f : Address n → Address n → Bool) (x y : Address n) (hf : f x y = false) :
    FiniteKrausChannel.FullDiamondErrorAtMost
      (((exactPhaseRoutingProcess f).recoverAlice x y).comp
        ((exactPhaseRoutingProcess f).alicePreRecovery x y))
      FiniteKrausChannel.identity 0 :=
  FiniteKrausChannel.fullDiamondErrorAtMost_of_action_eq _ _ _ 0
    (fun Q ↦ (exactPhaseRoutingProcess_alice f x y hf Q).trans
      (FiniteKrausChannel.identity_action Q).symm)
    identity_zeroError

/-- Bob's exactness includes inputs entangled with an arbitrary finite reference. -/
theorem exactPhaseRoutingProcess_bob_zeroError
    (f : Address n → Address n → Bool) (x y : Address n) (hf : f x y = true) :
    FiniteKrausChannel.FullDiamondErrorAtMost
      (((exactPhaseRoutingProcess f).recoverBob x y).comp
        ((exactPhaseRoutingProcess f).bobPreRecovery x y))
      FiniteKrausChannel.identity 0 :=
  FiniteKrausChannel.fullDiamondErrorAtMost_of_action_eq _ _ _ 0
    (fun Q ↦ (exactPhaseRoutingProcess_bob f x y hf Q).trans
      (FiniteKrausChannel.identity_action Q).symm)
    identity_zeroError

/-- The raw shared state has full marginal support on \(2n+2\) qubits
per side. The work and Bell pairs prepared locally are outside this cut. -/
theorem exactPhaseRoutingProcess_resourceDimension (f : Address n → Address n → Bool) :
    sharedResourceDimension (exactPhaseRoutingProcess f).rhoLR = 2 ^ (2 * n + 2) := by
  apply SchmidtRaw.resourceDimension_eq_of_pos
  intro j
  rw [exactPhaseRouterNormalized_weight]
  positivity

/-- The charged logarithmic resource cost of the exact router is \(2n+2\). -/
theorem exactPhaseRoutingProcess_resourceCost (f : Address n → Address n → Bool) :
    sharedResourceCost (exactPhaseRoutingProcess f).rhoLR = (2 * n + 2 : ℝ) := by
  unfold sharedResourceCost
  rw [exactPhaseRoutingProcess_resourceDimension, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  norm_cast

end

end LinearRouting.ExactPhase
