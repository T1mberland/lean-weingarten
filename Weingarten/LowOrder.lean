import Weingarten.Integration

/-! # Explicit low-order checks of the general Weingarten formula -/

set_option autoImplicit false

open scoped BigOperators Matrix ComplexOrder
open Matrix MeasureTheory

namespace Weingarten

noncomputable section

/-- Order zero has Gram matrix and Weingarten matrix `[1]`, including in dimension zero. -/
theorem weingartenMatrix_fin_zero {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm (Fin 0)) : weingartenMatrix (Fin 0) α σ τ = 1 := by
  have hG : gramMatrix (ι := Fin 0) (α := α) = 1 := by
    ext a b
    rw [Subsingleton.elim b a, gramMatrix_diag]
    simp
  rw [weingartenMatrix_eq_inv (Function.Embedding.ofIsEmpty : Fin 0 ↪ α), hG]
  simp [Subsingleton.elim σ τ]

/-- At order one the unique Weingarten coefficient is the reciprocal dimension. -/
theorem weingartenMatrix_fin_one {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (σ τ : Equiv.Perm (Fin 1)) :
    weingartenMatrix (Fin 1) α σ τ = (Fintype.card α : ℂ)⁻¹ := by
  have hd0 : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hG (a b : Equiv.Perm (Fin 1)) :
      gramMatrix (α := α) a b = (Fintype.card α : ℂ) := by
    rw [Subsingleton.elim b a, gramMatrix_diag]
    simp
  let B : Matrix (Equiv.Perm (Fin 1)) (Equiv.Perm (Fin 1)) ℂ :=
    fun _ _ => (Fintype.card α : ℂ)⁻¹
  have hGB : gramMatrix (α := α) * B = 1 := by
    ext a b
    simp [Matrix.mul_apply, B, hG, hd0, Matrix.one_apply, Subsingleton.elim a b]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using Fintype.card_pos (α := α) : Fintype.card (Fin 1) ≤ Fintype.card α)
  rw [weingartenMatrix_eq_inv e, Matrix.inv_eq_right_inv hGB]

private theorem sum_perm_two (f : Equiv.Perm (Fin 2) → ℂ) :
    (∑ σ, f σ) = f 1 + f (Equiv.swap 0 1) := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [h]
  simp [show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide]

private theorem perm_two_cases (ρ : Equiv.Perm (Fin 2)) :
    ρ = 1 ∨ ρ = Equiv.swap 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hm := Finset.mem_univ ρ
  rw [h, Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm

/-- The order-two Gram matrix has diagonal `d²` and off-diagonal `d`. -/
theorem gramMatrix_fin_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm (Fin 2)) :
    gramMatrix (α := α) σ τ =
      if σ = τ then (Fintype.card α : ℂ) ^ 2 else (Fintype.card α : ℂ) := by
  rcases perm_two_cases σ with rfl | rfl <;> rcases perm_two_cases τ with rfl | rfl
  · simp
  · rw [gramMatrix_apply, ← (finTwoArrowEquiv α).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    simp [finTwoArrowEquiv, funext_iff,
      Fin.forall_fin_two, Function.comp_def, eq_comm]
  · rw [gramMatrix_apply, ← (finTwoArrowEquiv α).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    simp [finTwoArrowEquiv, funext_iff,
      Fin.forall_fin_two, Function.comp_def, eq_comm]
  · simp

/-- The usual order-two coefficients, with the necessary `d ≥ 2` condition. -/
theorem weingartenMatrix_fin_two {α : Type*} [Fintype α] [DecidableEq α]
    (hd : 2 ≤ Fintype.card α) (σ τ : Equiv.Perm (Fin 2)) :
    weingartenMatrix (Fin 2) α σ τ =
      if σ = τ then 1 / ((Fintype.card α : ℂ) ^ 2 - 1)
      else -1 / ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) ^ 2 - 1)) := by
  set d : ℂ := (Fintype.card α : ℂ) with hddef
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hd2 : d ^ 2 - 1 ≠ 0 := by
    have hn : 1 < Fintype.card α ^ 2 := by nlinarith
    have hc : (Fintype.card α : ℂ) ^ 2 ≠ 1 := by
      exact_mod_cast (ne_of_gt hn)
    exact sub_ne_zero.mpr hc
  let B : Matrix (Equiv.Perm (Fin 2)) (Equiv.Perm (Fin 2)) ℂ :=
    fun a b => if a = b then 1 / (d ^ 2 - 1) else -1 / (d * (d ^ 2 - 1))
  have hGB : gramMatrix (α := α) * B = 1 := by
    ext a b
    simp only [Matrix.mul_apply, sum_perm_two, gramMatrix_fin_two]
    rcases perm_two_cases a with rfl | rfl <;> rcases perm_two_cases b with rfl | rfl
    all_goals
      norm_num [B, Matrix.one_apply,
        show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide,
        show Equiv.swap (0 : Fin 2) 1 ≠ 1 by decide, ← hddef]
      field_simp [hd0, hd2]
      ring
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (by simpa using hd :
    Fintype.card (Fin 2) ≤ Fintype.card α)
  rw [weingartenMatrix_eq_inv e, Matrix.inv_eq_right_inv hGB]

/-- The four-delta formula follows by evaluating the two permutation sums. -/
theorem integral_unitary_two {α : Type*} [Fintype α] [DecidableEq α]
    (hd : 2 ≤ Fintype.card α) (i j i' j' : Fin 2 → α) :
    (∫ U : UnitaryGroup α,
      (∏ a, U (i a) (j a)) * star (∏ a, U (i' a) (j' a)) ∂haar α) =
      (pairing 1 i i' * pairing 1 j j' +
        pairing (Equiv.swap 0 1) i i' * pairing (Equiv.swap 0 1) j j') /
          ((Fintype.card α : ℂ) ^ 2 - 1) -
      (pairing 1 i i' * pairing (Equiv.swap 0 1) j j' +
        pairing (Equiv.swap 0 1) i i' * pairing 1 j j') /
          ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) ^ 2 - 1)) := by
  rw [integral_unitary_weingarten]
  simp [sum_perm_two, weingartenMatrix_fin_two hd,
    show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide,
    show Equiv.swap (0 : Fin 2) 1 ≠ 1 by decide]
  ring

/-- In the singular case `d = 1, k = 2`, all four pseudoinverse entries are `1/4`. -/
theorem weingartenMatrix_one_two (σ τ : Equiv.Perm (Fin 2)) :
    weingartenMatrix (Fin 2) (Fin 1) σ τ = 1 / 4 := by
  have hG : gramMatrix (ι := Fin 2) (α := Fin 1) = fun _ _ => (1 : ℂ) := by
    ext a b
    simp [gramMatrix_fin_two]
  have h := spectralInverse_eq_of_penrose
    (gramMatrix_posSemidef (ι := Fin 2) (α := Fin 1)).isHermitian
    (B := fun _ _ => (1 / 4 : ℂ))
  have he : weingartenMatrix (Fin 2) (Fin 1) = fun _ _ => (1 / 4 : ℂ) := by
    apply h
    all_goals
      ext a b
      norm_num [hG, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.card_perm]
  exact congr_fun (congr_fun he σ) τ

/-- A singular fourth moment evaluated through the general integration theorem. -/
theorem integral_one_two (i j i' j' : Fin 2 → Fin 1) :
    (∫ U : UnitaryGroup (Fin 1),
      (∏ a, U (i a) (j a)) * star (∏ a, U (i' a) (j' a)) ∂haar (Fin 1)) = 1 := by
  rw [integral_unitary_weingarten]
  simp only [weingartenMatrix_one_two]
  have hp (σ : Equiv.Perm (Fin 2)) (a b : Fin 2 → Fin 1) : pairing σ a b = 1 := by
    simp [pairing, Subsingleton.elim b (a ∘ σ)]
  simp only [hp, one_mul, mul_one, sum_perm_two]
  norm_num

end

end Weingarten
