import LinearRouting.FiniteKrausPartialTrace

/-!
# The global channel of two local isometries with a shared Schmidt source

The first round appends the shared source, applies the two local isometries,
and regroups the output registers so that each party has its local register
and the message it received.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder Kronecker

universe uX uY uA uXM uYK uBM

variable {X : Type uX} {Y : Type uY}
variable {Akeep : Type uA} {Xmsg : Type uXM}
variable {Ykeep : Type uYK} {Bmsg : Type uBM}
variable [Fintype Akeep] [DecidableEq Akeep]
variable [Fintype Xmsg] [DecidableEq Xmsg]
variable [Fintype Ykeep] [DecidableEq Ykeep]
variable [Fintype Bmsg] [DecidableEq Bmsg]

/-- Regroup the local outputs into Bob's and Alice's receiver registers. -/
def schmidtProtocolOutputRegroup :
    ((Akeep × Xmsg) × (Ykeep × Bmsg)) ≃
      ((Xmsg × Ykeep) × (Akeep × Bmsg)) where
  toFun p := ((p.1.2, p.2.1), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.1), (p.1.2, p.2.2))
  left_inv p := by rcases p with ⟨⟨a, xm⟩, yk, b⟩; rfl
  right_inv p := by rcases p with ⟨⟨xm, yk⟩, a, b⟩; rfl

/-- Embed the computational qubit together with a Schmidt vector into the two
local input registers. -/
noncomputable def schmidtProtocolInputIsometry {d : ℕ}
    (lam : Fin d → ℝ) :
    Matrix ((Fin 2 × Fin d) × Fin d) (Fin 2) ℂ :=
  fun p q ↦ if p.1.1 = q ∧ p.1.2 = p.2 then
    (Real.sqrt (lam p.1.2) : ℂ) else 0

/-- Normalization of the Schmidt weights makes the input embedding an
isometry. -/
theorem schmidtProtocolInputIsometry_isometry {d : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1) :
    (schmidtProtocolInputIsometry lam)ᴴ *
        schmidtProtocolInputIsometry lam = 1 := by
  classical
  ext q q'
  fin_cases q <;> fin_cases q' <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      schmidtProtocolInputIsometry, Fintype.sum_prod_type,
      Fin.sum_univ_two]
  all_goals
    calc
      ∑ r : Fin d, (Real.sqrt (lam r) : ℂ) *
          (Real.sqrt (lam r) : ℂ) =
          ∑ r : Fin d, (lam r : ℂ) := by
        apply Finset.sum_congr rfl
        intro r _hr
        norm_cast
        exact Real.mul_self_sqrt (hlam r)
      _ = 1 := by exact_mod_cast hlamSum

/-- The tensor product of Alice's and Bob's first-round isometries. -/
noncomputable def schmidtProtocolLocalTensorIsometry {d : ℕ}
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (x : X) (y : Y) :
    Matrix ((Akeep × Xmsg) × (Ykeep × Bmsg))
      ((Fin 2 × Fin d) × Fin d) ℂ :=
  Alice x ⊗ₖ Bob y

omit [DecidableEq Akeep] [DecidableEq Xmsg]
    [DecidableEq Ykeep] [DecidableEq Bmsg] in
/-- The tensor product of the two local first-round maps is an isometry. -/
theorem schmidtProtocolLocalTensorIsometry_isometry {d : ℕ}
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    (schmidtProtocolLocalTensorIsometry Alice Bob x y)ᴴ *
        schmidtProtocolLocalTensorIsometry Alice Bob x y = 1 := by
  rw [schmidtProtocolLocalTensorIsometry, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hAlice x, hBob y,
    Matrix.one_kronecker_one]

/-- The complete first-round isometry before output regrouping. -/
noncomputable def schmidtProtocolUnregroupedIsometry {d : ℕ}
    (lam : Fin d → ℝ)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (x : X) (y : Y) :
    Matrix ((Akeep × Xmsg) × (Ykeep × Bmsg)) (Fin 2) ℂ :=
  schmidtProtocolLocalTensorIsometry Alice Bob x y *
    schmidtProtocolInputIsometry lam

omit [DecidableEq Akeep] [DecidableEq Xmsg]
    [DecidableEq Ykeep] [DecidableEq Bmsg] in
/-- The unregrouped global map is an isometry. -/
theorem schmidtProtocolUnregroupedIsometry_isometry {d : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    (schmidtProtocolUnregroupedIsometry lam Alice Bob x y)ᴴ *
        schmidtProtocolUnregroupedIsometry lam Alice Bob x y = 1 := by
  rw [schmidtProtocolUnregroupedIsometry, Matrix.conjTranspose_mul]
  calc
    (schmidtProtocolInputIsometry lam)ᴴ *
        (schmidtProtocolLocalTensorIsometry Alice Bob x y)ᴴ *
        (schmidtProtocolLocalTensorIsometry Alice Bob x y *
          schmidtProtocolInputIsometry lam) =
        (schmidtProtocolInputIsometry lam)ᴴ *
          ((schmidtProtocolLocalTensorIsometry Alice Bob x y)ᴴ *
            schmidtProtocolLocalTensorIsometry Alice Bob x y) *
          schmidtProtocolInputIsometry lam := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [schmidtProtocolLocalTensorIsometry_isometry
        Alice Bob hAlice hBob x y, Matrix.mul_one,
        schmidtProtocolInputIsometry_isometry lam hlam hlamSum]

/-- The complete first-round isometry, regrouped as Bob's retained pair
followed by the two discarded local environments. -/
noncomputable def schmidtProtocolGlobalIsometry {d : ℕ}
    (lam : Fin d → ℝ)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (x : X) (y : Y) :
    Matrix ((Xmsg × Ykeep) × (Akeep × Bmsg)) (Fin 2) ℂ :=
  fun p q ↦ schmidtProtocolUnregroupedIsometry lam Alice Bob x y
    (schmidtProtocolOutputRegroup.symm p) q

omit [Fintype Akeep] [DecidableEq Akeep]
    [Fintype Xmsg] [DecidableEq Xmsg]
    [Fintype Ykeep] [DecidableEq Ykeep]
    [Fintype Bmsg] [DecidableEq Bmsg] in
theorem schmidtProtocolGlobalIsometry_apply {d : ℕ}
    (lam : Fin d → ℝ)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (x : X) (y : Y) (xm : Xmsg) (yk : Ykeep)
    (a : Akeep) (b : Bmsg) (q : Fin 2) :
    schmidtProtocolGlobalIsometry lam Alice Bob x y
        ((xm, yk), (a, b)) q =
      ∑ r : Fin d, Alice x (a, xm) (q, r) * Bob y (yk, b) r *
        (Real.sqrt (lam r) : ℂ) := by
  fin_cases q <;>
    simp [schmidtProtocolGlobalIsometry,
      schmidtProtocolUnregroupedIsometry,
      schmidtProtocolLocalTensorIsometry, schmidtProtocolInputIsometry,
      schmidtProtocolOutputRegroup, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

omit [DecidableEq Akeep] [DecidableEq Xmsg]
    [DecidableEq Ykeep] [DecidableEq Bmsg] in
/-- Output regrouping preserves the global isometry equation. -/
theorem schmidtProtocolGlobalIsometry_isometry {d : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    (schmidtProtocolGlobalIsometry lam Alice Bob x y)ᴴ *
        schmidtProtocolGlobalIsometry lam Alice Bob x y = 1 := by
  ext q q'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    schmidtProtocolGlobalIsometry]
  rw [Equiv.sum_comp schmidtProtocolOutputRegroup.symm
    (fun p ↦ star
      (schmidtProtocolUnregroupedIsometry lam Alice Bob x y p q) *
      schmidtProtocolUnregroupedIsometry lam Alice Bob x y p q')]
  exact congrFun (congrFun
    (schmidtProtocolUnregroupedIsometry_isometry
      lam hlam hlamSum Alice Bob hAlice hBob x y) q) q'

/-- The full one-Kraus channel induced by the shared Schmidt resource and the
two first-round local isometries. -/
noncomputable def schmidtProtocolGlobalChannel {d : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    FiniteKrausChannel (Fin 1) (Fin 2)
      ((Xmsg × Ykeep) × (Akeep × Bmsg)) :=
  FiniteKrausChannel.ofIsometry
    (schmidtProtocolGlobalIsometry lam Alice Bob x y)
    (schmidtProtocolGlobalIsometry_isometry
      lam hlam hlamSum Alice Bob hAlice hBob x y)

/-- Bob's pre-recovery channel discards Alice's receiver registers. -/
noncomputable def schmidtProtocolBobReducedChannel {d : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Akeep × Xmsg) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Ykeep × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    FiniteKrausChannel ((Fin 1) × (Akeep × Bmsg)) (Fin 2)
      (Xmsg × Ykeep) :=
  (FiniteKrausChannel.discardSecond (Xmsg × Ykeep) (Akeep × Bmsg)).comp
    (schmidtProtocolGlobalChannel lam hlam hlamSum
      Alice Bob hAlice hBob x y)

/-- Permutation isometry from a product basis to the standard
`Fin (n*m)` basis. -/
def productReindexIsometry (n m : ℕ) :
    Matrix (Fin (n * m)) (Fin n × Fin m) ℂ :=
  fun i p ↦ if i = finProdFinEquiv p then 1 else 0

theorem productReindexIsometry_isometry (n m : ℕ) :
    (productReindexIsometry n m)ᴴ * productReindexIsometry n m = 1 := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [productReindexIsometry, Matrix.mul_apply]
  · simp [productReindexIsometry, Matrix.mul_apply, hpq, Ne.symm hpq]

/-- The one-Kraus basis permutation channel from a product carrier to a
standard finite carrier. -/
noncomputable def productReindexChannel (n m : ℕ) :
    FiniteKrausChannel (Fin 1) (Fin n × Fin m) (Fin (n * m)) :=
  FiniteKrausChannel.ofIsometry (productReindexIsometry n m)
    (productReindexIsometry_isometry n m)

theorem productReindexChannel_action {n m : ℕ}
    (M : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (productReindexChannel n m).action M = reindexProductMatrix M := by
  rw [productReindexChannel, FiniteKrausChannel.ofIsometry_action]
  ext i j
  have hsum (k : Fin (n * m)) (f : (Fin n × Fin m) → ℂ) :
      ∑ p, (if k = finProdFinEquiv p then f p else 0) =
        f (finProdFinEquiv.symm k) := by
    rw [Finset.sum_eq_single (finProdFinEquiv.symm k)]
    · rw [if_pos (Equiv.apply_symm_apply finProdFinEquiv k).symm]
    · intro p _hp hp
      have hne : k ≠ finProdFinEquiv p := by
        intro h
        apply hp
        exact (finProdFinEquiv.injective
          ((Equiv.apply_symm_apply finProdFinEquiv k).trans h)).symm
      simp [hne]
    · intro hk
      exact (hk (Finset.mem_univ _)).elim
  simp only [productReindexIsometry, reindexProductMatrix,
    Matrix.reindex_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
  have hstar (P : Prop) [Decidable P] :
      star (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
    by_cases hP : P <;> simp [hP]
  simp_rw [hstar, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [hsum j, hsum i]

/-- Finite-indexed version of Bob's reduced global channel. -/
noncomputable def schmidtProtocolBobReducedFinChannel {d n m : ℕ}
    (lam : Fin d → ℝ) (hlam : ∀ r, 0 ≤ lam r)
    (hlamSum : ∑ r, lam r = 1)
    (Alice : X → Matrix (Akeep × Fin n) (Fin 2 × Fin d) ℂ)
    (Bob : Y → Matrix (Fin m × Bmsg) (Fin d) ℂ)
    (hAlice : ∀ x, (Alice x)ᴴ * Alice x = 1)
    (hBob : ∀ y, (Bob y)ᴴ * Bob y = 1)
    (x : X) (y : Y) :
    FiniteKrausChannel
      (((Fin 1) × (Akeep × Bmsg)) × Fin 1)
      (Fin 2) (Fin (n * m)) :=
  (productReindexChannel n m).comp
    (schmidtProtocolBobReducedChannel lam hlam hlamSum
      Alice Bob hAlice hBob x y)

end LinearRouting
