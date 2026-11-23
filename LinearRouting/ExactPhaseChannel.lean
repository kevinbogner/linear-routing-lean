import LinearRouting.FiniteKrausPartialTrace

/-!
# Exact recovery from a decoded amplitude factorization

If the decoded amplitudes factor into the input ket and an environment
independent of the input, every composite Kraus matrix is a scalar times the
identity. Completeness then gives the identity channel.
-/

namespace LinearRouting.ExactPhase

open Matrix FiniteKrausChannel
open scoped BigOperators

variable {I B A J : Type*}
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]
variable [Fintype J] [DecidableEq J]

omit [Nonempty I] in
private theorem discardSecondKraus_mul_apply {P E T : Type*}
    [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (V : Matrix (P × E) T ℂ) (p : P) (e : E) (t : T) :
    (discardSecondKraus P E e * V) p t = V (p, e) t := by
  simp [Matrix.mul_apply, discardSecondKraus, Fintype.sum_prod_type, ite_and, ite_mul,
    Finset.sum_ite_eq]

omit [Nonempty I] in
private theorem discardFirstKraus_mul_apply {P E T : Type*}
    [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (V : Matrix (P × E) T ℂ) (p : P) (e : E) (t : T) :
    (discardFirstKraus P E p * V) e t = V (p, e) t := by
  simp [Matrix.mul_apply, discardFirstKraus, Fintype.sum_prod_type, ite_and, ite_mul,
    Finset.sum_ite_eq]

private theorem scalarKraus_action_eq {K : Type*} [Fintype K]
    (Φ : FiniteKrausChannel K I I) (c : K → ℂ)
    (hKraus : ∀ k, Φ.kraus k = c k • 1) (Q : Matrix I I ℂ) :
    Φ.action Q = Q := by
  let i : I := Classical.choice inferInstance
  have hcompl := Φ.completeness
  simp_rw [hKraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hcompl
  have hnorm : (∑ k, star (c k) * c k) = 1 := by
    have hentry := congrArg (fun M : Matrix I I ℂ => M i i) hcompl
    simpa [Matrix.sum_apply, Matrix.smul_apply] using hentry
  rw [action_apply]
  calc
    _ = ∑ k, (c k * star (c k)) • Q := by
      simp_rw [hKraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    _ = Q := by
      simp_rw [mul_comm (c _)]
      rw [← Finset.sum_smul, hnorm, one_smul]

/-- Decode the first factor of the split isometry, then discard the decoder's
environment. The factored amplitudes give the identity channel. -/
theorem decodeFirst_action_eq
    (G : Matrix (B × A) I ℂ) (D : Matrix (I × J) B ℂ)
    (hG : Gᴴ * G = 1) (hD : Dᴴ * D = 1) (coeff : J → A → ℂ)
    (hfactor : ∀ (o : I) (j : J) (a : A) (q : I),
      (∑ b, D (o, j) b * G (b, a) q) = if o = q then coeff j a else 0)
    (Q : Matrix I I ℂ) :
    (((discardSecond I J).comp (ofIsometry D hD)).comp
      ((discardSecond B A).comp (ofIsometry G hG))).action Q = Q := by
  refine scalarKraus_action_eq _ (fun k => coeff k.2.2 k.1.2) ?_ Q
  intro ⟨⟨kg, a⟩, ⟨kd, j⟩⟩
  ext o q
  change ((discardSecondKraus I J j * D) * (discardSecondKraus B A a * G)) o q =
    (coeff j a • (1 : Matrix I I ℂ)) o q
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  change (∑ b, (discardSecondKraus I J j * D) o b *
      (discardSecondKraus B A a * G) b q) =
    coeff j a * (if o = q then 1 else 0)
  simp only [discardSecondKraus_mul_apply, hfactor]
  split <;> simp

/-- Decode the second factor of the split isometry, then discard the decoder's
environment. The factored amplitudes give the identity channel. -/
theorem decodeSecond_action_eq
    (G : Matrix (B × A) I ℂ) (D : Matrix (I × J) A ℂ)
    (hG : Gᴴ * G = 1) (hD : Dᴴ * D = 1) (coeff : J → B → ℂ)
    (hfactor : ∀ (o : I) (j : J) (b : B) (q : I),
      (∑ a, D (o, j) a * G (b, a) q) = if o = q then coeff j b else 0)
    (Q : Matrix I I ℂ) :
    (((discardSecond I J).comp (ofIsometry D hD)).comp
      ((discardFirst B A).comp (ofIsometry G hG))).action Q = Q := by
  refine scalarKraus_action_eq _ (fun k => coeff k.2.2 k.1.2) ?_ Q
  intro ⟨⟨kg, b⟩, ⟨kd, j⟩⟩
  ext o q
  change ((discardSecondKraus I J j * D) * (discardFirstKraus B A b * G)) o q =
    (coeff j b • (1 : Matrix I I ℂ)) o q
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  change (∑ a, (discardSecondKraus I J j * D) o a *
      (discardFirstKraus B A b * G) a q) =
    coeff j b * (if o = q then 1 else 0)
  simp only [discardSecondKraus_mul_apply, discardFirstKraus_mul_apply, hfactor]
  split <;> simp

end LinearRouting.ExactPhase
