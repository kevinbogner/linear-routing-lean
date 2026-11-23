import LinearRouting.DensityMatrix

/-!
# Finite Kraus channels

This file provides an elementary finite-dimensional channel interface for
complex matrices.  A channel is represented by a finite family of rectangular
Kraus matrices satisfying the trace-preserving completeness relation.  The
construction is internal and uses no external channel or complete-positivity
assumption.
-/

namespace LinearRouting

open Matrix
open scoped BigOperators ComplexOrder

universe uK uL uI uM uO

/-- A finite Kraus representation of a trace-preserving channel from input
basis `I` to output basis `O`.  A Kraus matrix has rows indexed by `O` and
columns indexed by `I`. -/
structure FiniteKrausChannel
    (K : Type uK) [Fintype K]
    (I : Type uI) (O : Type uO)
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] where
  kraus : K → Matrix O I ℂ
  completeness : ∑ k, (kraus k)ᴴ * kraus k = 1

namespace FiniteKrausChannel

variable {K : Type uK} [Fintype K]
variable {L : Type uL} [Fintype L]
variable {I : Type uI} {M : Type uM} {O : Type uO}
variable [Fintype I] [DecidableEq I]
variable [Fintype M] [DecidableEq M]
variable [Fintype O] [DecidableEq O]

/-- Conjugation by one rectangular Kraus matrix as a complex-linear map. -/
def conjugationLinear (V : Matrix O I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq I] [Fintype O] [DecidableEq O] in
@[simp]
theorem conjugationLinear_apply (V : Matrix O I ℂ) (X : Matrix I I ℂ) :
    conjugationLinear V X = V * X * Vᴴ := rfl

/-- Complex-linear action of a finite Kraus family. -/
noncomputable def action (Phi : FiniteKrausChannel K I O) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  ∑ k, conjugationLinear (Phi.kraus k)

@[simp]
theorem action_apply (Phi : FiniteKrausChannel K I O)
    (X : Matrix I I ℂ) :
    Phi.action X = ∑ k, Phi.kraus k * X * (Phi.kraus k)ᴴ := by
  simp [action]

/-- Explicit additivity of the channel action. -/
theorem action_add (Phi : FiniteKrausChannel K I O)
    (X Y : Matrix I I ℂ) :
    Phi.action (X + Y) = Phi.action X + Phi.action Y :=
  map_add Phi.action X Y

/-- Explicit complex homogeneity of the channel action. -/
theorem action_smul (Phi : FiniteKrausChannel K I O)
    (c : ℂ) (X : Matrix I I ℂ) :
    Phi.action (c • X) = c • Phi.action X :=
  map_smul Phi.action c X

/-- Every finite Kraus action preserves positive semidefiniteness. -/
theorem action_posSemidef (Phi : FiniteKrausChannel K I O)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    (Phi.action X).PosSemidef := by
  rw [action_apply]
  classical
  induction (Finset.univ : Finset K) using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix O O ℂ).PosSemidef)
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (hX.mul_mul_conjTranspose_same (Phi.kraus k)).add ih

/-- Every finite Kraus action preserves Hermiticity. -/
theorem action_isHermitian (Phi : FiniteKrausChannel K I O)
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Phi.action X).IsHermitian := by
  rw [action_apply]
  classical
  induction (Finset.univ : Finset K) using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (Matrix.isHermitian_mul_mul_conjTranspose (Phi.kraus k) hX).add ih

omit [DecidableEq I] [DecidableEq O] in
private theorem trace_kraus_term (V : Matrix O I ℂ)
    (X : Matrix I I ℂ) :
    (V * X * Vᴴ).trace = (X * (Vᴴ * V)).trace := by
  calc
    (V * X * Vᴴ).trace = (V * (X * Vᴴ)).trace := by
      rw [Matrix.mul_assoc]
    _ = ((X * Vᴴ) * V).trace := Matrix.trace_mul_comm _ _
    _ = (X * (Vᴴ * V)).trace := by rw [Matrix.mul_assoc]

/-- The Kraus completeness relation implies trace preservation. -/
theorem trace_action (Phi : FiniteKrausChannel K I O)
    (X : Matrix I I ℂ) :
    (Phi.action X).trace = X.trace := by
  rw [action_apply, Matrix.trace_sum]
  simp_rw [trace_kraus_term]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, Phi.completeness,
    Matrix.mul_one]

private theorem comp_completeness
    (Psi : FiniteKrausChannel L M O)
    (Phi : FiniteKrausChannel K I M) :
    ∑ p : K × L,
        (Psi.kraus p.2 * Phi.kraus p.1)ᴴ *
          (Psi.kraus p.2 * Phi.kraus p.1) = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ k, ∑ l,
        (Psi.kraus l * Phi.kraus k)ᴴ *
          (Psi.kraus l * Phi.kraus k)) =
        ∑ k, (Phi.kraus k)ᴴ *
          (∑ l, (Psi.kraus l)ᴴ * Psi.kraus l) * Phi.kraus k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ l, (Psi.kraus l * Phi.kraus k)ᴴ *
            (Psi.kraus l * Phi.kraus k)) =
            ∑ l, (Phi.kraus k)ᴴ *
              ((Psi.kraus l)ᴴ * Psi.kraus l) * Phi.kraus k := by
          apply Finset.sum_congr rfl
          intro l hl
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (Phi.kraus k)ᴴ *
            (∑ l, (Psi.kraus l)ᴴ * Psi.kraus l) * Phi.kraus k := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ k, (Phi.kraus k)ᴴ * Phi.kraus k := by
      rw [Psi.completeness]
      simp
    _ = 1 := Phi.completeness

/-- Composition of finite Kraus channels.  The composite Kraus family is
indexed by the Cartesian product of the two finite index types. -/
noncomputable def comp
    (Psi : FiniteKrausChannel L M O)
    (Phi : FiniteKrausChannel K I M) :
    FiniteKrausChannel (K × L) I O where
  kraus p := Psi.kraus p.2 * Phi.kraus p.1
  completeness := comp_completeness Psi Phi

@[simp]
theorem comp_kraus
    (Psi : FiniteKrausChannel L M O)
    (Phi : FiniteKrausChannel K I M) (p : K × L) :
    (Psi.comp Phi).kraus p = Psi.kraus p.2 * Phi.kraus p.1 := rfl

/-- The action of the composite Kraus family is composition of the two
complex-linear channel actions. -/
theorem comp_action
    (Psi : FiniteKrausChannel L M O)
    (Phi : FiniteKrausChannel K I M) (X : Matrix I I ℂ) :
    (Psi.comp Phi).action X = Psi.action (Phi.action X) := by
  rw [action_apply, action_apply, action_apply, Fintype.sum_prod_type]
  calc
    (∑ k, ∑ l,
        (Psi.kraus l * Phi.kraus k) * X *
          ((Psi.kraus l * Phi.kraus k)ᴴ)) =
        ∑ l, ∑ k, Psi.kraus l *
          (Phi.kraus k * X * (Phi.kraus k)ᴴ) * (Psi.kraus l)ᴴ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ l, Psi.kraus l *
        (∑ k, Phi.kraus k * X * (Phi.kraus k)ᴴ) * (Psi.kraus l)ᴴ := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Matrix.mul_sum, Matrix.sum_mul]

/-- Linear-map form of `comp_action`. -/
theorem comp_action_eq
    (Psi : FiniteKrausChannel L M O)
    (Phi : FiniteKrausChannel K I M) :
    (Psi.comp Phi).action = Psi.action.comp Phi.action := by
  apply LinearMap.ext
  intro X
  exact comp_action Psi Phi X

private theorem densityMatrix_ext {n : ℕ} {rho sigma : DensityMatrix n}
    (h : rho.val = sigma.val) : rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          simp only at h
          subst sigma
          rfl

/-- A channel on `Fin`-indexed matrices maps the repository's bundled
`DensityMatrix` states to bundled density matrices. -/
noncomputable def mapDensity {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (rho : DensityMatrix n) : DensityMatrix m where
  val := Phi.action rho.val
  posSemidef := Phi.action_posSemidef rho.posSemidef
  trace_eq_one := (Phi.trace_action rho.val).trans rho.trace_eq_one

@[simp]
theorem mapDensity_val {n m : ℕ}
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (rho : DensityMatrix n) :
    (Phi.mapDensity rho).val = Phi.action rho.val := rfl

/-- Mapping bundled states respects channel composition. -/
theorem mapDensity_comp {n m p : ℕ}
    (Psi : FiniteKrausChannel L (Fin m) (Fin p))
    (Phi : FiniteKrausChannel K (Fin n) (Fin m))
    (rho : DensityMatrix n) :
    (Psi.comp Phi).mapDensity rho = Psi.mapDensity (Phi.mapDensity rho) := by
  apply densityMatrix_ext
  exact comp_action Psi Phi rho.val

/-- A single isometry is a one-Kraus trace-preserving channel. -/
noncomputable def ofIsometry (V : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) : FiniteKrausChannel (Fin 1) I O where
  kraus := fun _ ↦ V
  completeness := by simpa using hV

@[simp]
theorem ofIsometry_action (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix I I ℂ) :
    (ofIsometry V hV).action X = V * X * Vᴴ := by
  simp [action_apply, ofIsometry]

/-- The identity channel as a single-Kraus channel. -/
noncomputable def identity : FiniteKrausChannel (Fin 1) I I :=
  ofIsometry (1 : Matrix I I ℂ) (by simp)

@[simp]
theorem identity_action (X : Matrix I I ℂ) :
    (identity : FiniteKrausChannel (Fin 1) I I).action X = X := by
  rw [identity, ofIsometry_action]
  simp

@[simp]
theorem identity_mapDensity {n : ℕ} (rho : DensityMatrix n) :
    (identity : FiniteKrausChannel (Fin 1) (Fin n) (Fin n)).mapDensity rho = rho := by
  apply densityMatrix_ext
  exact identity_action rho.val

end FiniteKrausChannel

end LinearRouting
