import LinearRouting.ExactPhaseBase
import LinearRouting.ExactPhaseTeleportation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Local first-round maps of the exact phase router

Both parties copy their measured labels into the two receiver registers.
The coherent version of copying gives first-round isometries. Each receiver
can read its copy in the computational basis.
-/

namespace LinearRouting.ExactPhase

open Matrix
open scoped BigOperators Kronecker

abbrev Key := Bool × Bool

abbrev Pair (I : Type*) := I × I
abbrev GadgetOut (L W : Type*) := L × Pair W
abbrev AliceData (W : Type*) := Key × Pair W
abbrev BobData (W : Type*) := Fin 2 × Pair W
abbrev AliceKeep (L W : Type*) := AliceData W × Pair L
abbrev AliceSend (L W : Type*) := BobData W × Pair L

variable {I O L W : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype L] [DecidableEq L]
  [Fintype W] [DecidableEq W]

/-- Copy Alice's flag into the sent and retained registers. -/
noncomputable def copyFlag
    (M : Matrix (I × (O × L)) W ℂ) :
    Matrix ((I × L) × (O × L)) W ℂ :=
  fun p q ↦ if p.1.2 = p.2.2 then M (p.1.1, p.2) q else 0

omit [Fintype W] [DecidableEq W] [DecidableEq I] [DecidableEq O] in
theorem copyFlag_gram (M : Matrix (I × (O × L)) W ℂ) :
    (copyFlag M)ᴴ * copyFlag M = Mᴴ * M := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, copyFlag]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_eq_single g]
  · simp
  · intro h _ hh
    simp [hh]
  · simp

/-- Copy both measured labels on Bob's side. -/
noncomputable def bobEncoder (S : Matrix L L ℂ) :
    Matrix (Pair L × Pair L) (Pair L) ℂ :=
  fun p q ↦ if p.1 = p.2 then (S ⊗ₖ S) p.1 q else 0

theorem bobEncoder_isometry (S : Matrix L L ℂ) (hS : Sᴴ * S = 1) :
    (bobEncoder S)ᴴ * bobEncoder S = 1 := by
  have ht : (S ⊗ₖ S)ᴴ * (S ⊗ₖ S) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hS,
      Matrix.one_kronecker_one]
  ext i j
  rw [← ht]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bobEncoder]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

/-- The work pair's amplitude after applying the controlled operator to the
sent half of a local maximally entangled pair and changing the flag basis. -/
noncomputable def localGadget (F : Matrix L L ℂ) (T : L → Matrix W W ℂ) :
    Matrix (GadgetOut L W) L ℂ :=
  fun o j ↦ F o.1 j * (flatAmplitude (Fintype.card W) * T j o.2.1 o.2.2)

private theorem workAmplitude_normalized [Nonempty W] (U : Matrix W W ℂ)
    (hU : Uᴴ * U = 1) :
    ∑ p : Pair W, star (flatAmplitude (Fintype.card W) * U p.1 p.2) *
      (flatAmplitude (Fintype.card W) * U p.1 p.2) = 1 := by
  let a := flatAmplitude (Fintype.card W)
  change ∑ p : Pair W, star (a * U p.1 p.2) * (a * U p.1 p.2) = 1
  have ha : star a = a := star_flatAmplitude _
  have hu : ∀ v : W, ∑ u : W, star (U u v) * U u v = 1 := by
    intro v
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun₂ hU v v
  calc
    _ = (a * a) * ∑ p : Pair W, star (U p.1 p.2) * U p.1 p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [star_mul, ha]
      ring
    _ = a * a * (Fintype.card W : ℂ) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [hu]
      simp
    _ = 1 := flatAmplitude_mul_self_mul_card Fintype.card_ne_zero

theorem localGadget_isometry [Nonempty W] (F : Matrix L L ℂ)
    (hF : Fᴴ * F = 1) (T : L → Matrix W W ℂ)
    (hT : ∀ j, (T j)ᴴ * T j = 1) :
    (localGadget F T)ᴴ * localGadget F T = 1 := by
  ext i j
  let v (j : L) (p : Pair W) := flatAmplitude (Fintype.card W) * T j p.1 p.2
  have hf : (∑ h, star (F h i) * F h j) = (1 : Matrix L L ℂ) i j := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun₂ hF i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localGadget]
  change (∑ o : GadgetOut L W, star (F o.1 i * v i o.2) *
    (F o.1 j * v j o.2)) = _
  calc
    _ = (∑ h, star (F h i) * F h j) *
        (∑ p : Pair W, star (v i p) * v j p) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [star_mul]
      ring
    _ = _ := by
      rw [hf]
      by_cases hij : i = j
      · subst j
        rw [workAmplitude_normalized (T i) (hT i), mul_one]
      · simp [hij]

/-- The local teleportation preparation and both work gadgets for a key.
Summing the four Gram matrices gives the isometry relation. -/
noncomputable def aliceKeyBlock (F : Matrix L L ℂ)
    (T : Bool → L → Matrix W W ℂ) (k : Key) :
    Matrix (Fin 2 × Pair (GadgetOut L W)) (Fin 2 × Pair L) ℂ :=
  ((2 : ℂ)⁻¹ • pauli k) ⊗ₖ
    (localGadget F (T k.1) ⊗ₖ localGadget F (T k.2))

private theorem aliceKeyBlock_gram [Nonempty W] (F : Matrix L L ℂ)
    (hF : Fᴴ * F = 1) (T : Bool → L → Matrix W W ℂ)
    (hT : ∀ z j, (T z j)ᴴ * T z j = 1) (k : Key) :
    (aliceKeyBlock F T k)ᴴ * aliceKeyBlock F T k = (4 : ℂ)⁻¹ • 1 := by
  have hp : ((2 : ℂ)⁻¹ • pauli k)ᴴ * ((2 : ℂ)⁻¹ • pauli k) =
      (4 : ℂ)⁻¹ • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      pauli_conjTranspose_mul, smul_smul]
    norm_num
  unfold aliceKeyBlock
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    localGadget_isometry F hF (T k.1) (hT k.1),
    localGadget_isometry F hF (T k.2) (hT k.2),
    Matrix.one_kronecker_one, hp, Matrix.smul_kronecker, Matrix.one_kronecker_one]

private def aliceRegroup :
    (AliceData W × (BobData W × Pair L)) ≃
      (Key × (Fin 2 × Pair (GadgetOut L W))) where
  toFun p := (p.1.1, p.2.1.1,
    (p.2.2.1, p.2.1.2.1, p.1.2.1),
    (p.2.2.2, p.2.1.2.2, p.1.2.2))
  invFun p := ((p.1, p.2.2.1.2.2, p.2.2.2.2.2),
    (p.2.1, p.2.2.1.2.1, p.2.2.2.2.1), (p.2.2.1.1, p.2.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def aliceUncopied (F : Matrix L L ℂ)
    (T : Bool → L → Matrix W W ℂ) :
    Matrix (AliceData W × (BobData W × Pair L)) (Fin 2 × Pair L) ℂ :=
  fun o q ↦ aliceKeyBlock F T (aliceRegroup o).1 (aliceRegroup o).2 q

private theorem aliceUncopied_isometry [Nonempty W] (F : Matrix L L ℂ)
    (hF : Fᴴ * F = 1) (T : Bool → L → Matrix W W ℂ)
    (hT : ∀ z j, (T z j)ᴴ * T z j = 1) :
    (aliceUncopied F T)ᴴ * aliceUncopied F T = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, aliceUncopied]
  rw [Equiv.sum_comp aliceRegroup (fun p ↦
    star (aliceKeyBlock F T p.1 p.2 i) * aliceKeyBlock F T p.1 p.2 j),
    Fintype.sum_prod_type]
  change (∑ k, ((aliceKeyBlock F T k)ᴴ * aliceKeyBlock F T k) i j) = _
  simp_rw [aliceKeyBlock_gram F hF T hT]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Fintype.card_prod]

/-- Alice keeps the coherent teleportation key and the purifying work halves,
and sends the Pauli-padded qubit and the other halves. -/
noncomputable def aliceEncoder (F : Matrix L L ℂ) (T : Bool → L → Matrix W W ℂ) :
    Matrix (AliceKeep L W × AliceSend L W) (Fin 2 × Pair L) ℂ :=
  copyFlag (aliceUncopied F T)

theorem aliceEncoder_isometry [Nonempty W] (F : Matrix L L ℂ)
    (hF : Fᴴ * F = 1) (T : Bool → L → Matrix W W ℂ)
    (hT : ∀ z j, (T z j)ᴴ * T z j = 1) :
    (aliceEncoder F T)ᴴ * aliceEncoder F T = 1 := by
  rw [aliceEncoder, copyFlag_gram, aliceUncopied_isometry F hF T hT]

omit [Fintype L] [DecidableEq W] in
theorem aliceEncoder_apply (F : Matrix L L ℂ) (T : Bool → L → Matrix W W ℂ)
    (k : Key) (c q : Fin 2) (p p' : Pair W) (g h j : Pair L) :
    aliceEncoder F T (((k, p'), g), ((c, p), h)) (q, j) =
      if g = h then (2 : ℂ)⁻¹ * pauli k c q *
        localGadget F (T k.1) (h.1, p.1, p'.1) j.1 *
        localGadget F (T k.2) (h.2, p.2, p'.2) j.2 else 0 := by
  unfold aliceEncoder copyFlag aliceUncopied aliceKeyBlock aliceRegroup
  by_cases hgh : g = h <;> simp [hgh, mul_assoc]

end LinearRouting.ExactPhase
