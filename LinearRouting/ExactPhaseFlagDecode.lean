import Mathlib

/-!
# Decoding under copied flags

The decoder leaves both flags in the discarded registers and applies the
decoder for that pair of flags to the data registers.
-/

namespace LinearRouting.ExactPhase

open Matrix

variable {F K J : Type*} [DecidableEq F]

/-- The decoder selected by the two input flags, which are copied to the output. -/
def flagDecode (D : F × F → Matrix (Fin 2 × J) K ℂ) :
    Matrix (Fin 2 × (J × (F × F))) ((K × F) × F) ℂ :=
  Matrix.of fun out input ↦
    if out.2.2 = (input.1.2, input.2) then D out.2.2 (out.1, out.2.1) input.1.1
    else 0

@[simp] theorem flagDecode_apply (D : F × F → Matrix (Fin 2 × J) K ℂ)
    (out : Fin 2 × (J × (F × F))) (input : (K × F) × F) :
    flagDecode D out input =
      if out.2.2 = (input.1.2, input.2) then D out.2.2 (out.1, out.2.1) input.1.1
      else 0 := rfl

/-- The decoder acts isometrically on each flag component. -/
theorem flagDecode_isometry [Fintype F] [Fintype J] [DecidableEq K]
    (D : F × F → Matrix (Fin 2 × J) K ℂ) (hD : ∀ g, (D g)ᴴ * D g = 1) :
    (flagDecode D)ᴴ * flagDecode D = 1 := by
  ext ⟨⟨k, f₁⟩, f₂⟩ ⟨⟨l, g₁⟩, g₂⟩
  rw [Matrix.mul_apply, ← Equiv.sum_comp (Equiv.prodAssoc (Fin 2) J (F × F)),
    Fintype.sum_prod_type]
  simp only [Equiv.prodAssoc_apply, Matrix.conjTranspose_apply, flagDecode_apply]
  by_cases h : (f₁, f₂) = (g₁, g₂)
  · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    calc
      _ = ∑ oj : Fin 2 × J, star (D (f₁, f₂) oj k) * D (f₁, f₂) oj l := by
        refine Finset.sum_congr rfl fun oj _ ↦ ?_
        rw [Finset.sum_eq_single (f₁, f₂)]
        · simp
        · intro flag _ hflag
          simp [hflag]
        · simp
      _ = _ := by
        change ((D (f₁, f₂))ᴴ * D (f₁, f₂)) k l = _
        rw [hD]
        simp [Matrix.one_apply]
  · have hInput : ((k, f₁), f₂) ≠ ((l, g₁), g₂) := by
      intro h'
      exact h (congrArg (fun u : (K × F) × F ↦ (u.1.2, u.2)) h')
    rw [Matrix.one_apply_ne hInput]
    refine Finset.sum_eq_zero fun oj _ ↦ Finset.sum_eq_zero fun flag _ ↦ ?_
    by_cases hf : flag = (f₁, f₂)
    · have hg : flag ≠ (g₁, g₂) := fun h' ↦ h (hf.symm.trans h')
      simp [hg]
    · simp [hf]

/-- For a given output flag, only the matching input flag contributes. -/
theorem flagDecode_contract [Fintype K] [Fintype F]
    (D : F × F → Matrix (Fin 2 × J) K ℂ) (v : (K × F) × F → ℂ)
    (o : Fin 2) (j : J) (g : F × F) :
    (∑ input : (K × F) × F, flagDecode D (o, j, g) input * v input) =
      ∑ k, D g (o, j) k * v ((k, g.1), g.2) := by
  rw [← Equiv.sum_comp (Equiv.prodAssoc K F F).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Equiv.prodAssoc_symm_apply, flagDecode_apply]
  rw [Finset.sum_eq_single g]
  · simp
  · intro flag _ hflag
    simp [Ne.symm hflag]
  · simp

end LinearRouting.ExactPhase
