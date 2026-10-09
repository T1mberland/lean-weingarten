import Weingarten.Moments
import Weingarten.Permutation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

/-! # Tensor-power orthogonality and permutation contractions -/

open scoped BigOperators Matrix
open MeasureTheory

namespace Weingarten

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

/-- Row orthogonality for every tensor power, proved by factoring a sum over words. -/
theorem sum_entryProduct_mul_star (U : UnitaryGroup α) (i i' : Fin p → α) :
    (∑ j : Fin p → α, entryProduct i j U * star (entryProduct i' j U)) =
      if i = i' then 1 else 0 := by
  classical
  simp only [entryProduct, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a b => U (i a) b * star (U (i' a) b))]
  simp only [sum_row_mul_conj]
  by_cases h : i = i'
  · subst i'
    simp
  · rw [if_neg h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

/-- Move a permutation of columns to the inverse permutation of rows. -/
theorem entryProduct_comp (U : UnitaryGroup α) (i j : Fin p → α)
    (σ : Equiv.Perm (Fin p)) :
    entryProduct i (j ∘ σ) U = entryProduct (i ∘ σ.symm) j U := by
  unfold entryProduct
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (Equiv.prod_comp σ (fun a => U (i (σ.symm a)) (j a)))

/-- Unitary contraction with any permutation tensor, for all dimensions and orders. -/
theorem sum_mixedMonomial_pairing (U : UnitaryGroup α) (i i' : Fin p → α)
    (σ : Equiv.Perm (Fin p)) :
    (∑ j : Fin p → α, mixedMonomial i j i' (j ∘ σ) U) = pairing σ i i' := by
  simp only [mixedMonomial, entryProduct_comp, sum_entryProduct_mul_star, pairing]
  have h : i = i' ∘ σ.symm ↔ i' = i ∘ σ := by
    constructor
    · intro h
      funext a
      simpa using (congr_fun h (σ a)).symm
    · intro h
      funext a
      simpa using (congr_fun h (σ.symm a)).symm
  simp only [h]

/-- The actual Haar moment matrix fixes every permutation tensor. -/
theorem momentMatrix_mul_diagramMatrix :
    momentMatrix α p * diagramMatrix = diagramMatrix (ι := Fin p) (α := α) := by
  classical
  ext ⟨i, i'⟩ σ
  simp only [Matrix.mul_apply, momentMatrix, diagramMatrix, Fintype.sum_prod_type,
    pairing, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ j, ∫ U, mixedMonomial i j i' (j ∘ σ) U ∂haar α) = pairing σ i i'
  rw [← integral_finset_sum _ (fun j _ => integrable_mixedMonomial i j i' (j ∘ σ))]
  simp only [sum_mixedMonomial_pairing, integral_const, probReal_univ, one_smul]

/-- Inversion transposes and conjugates tensor-power coefficients. -/
theorem entryProduct_inv (U : UnitaryGroup α) (i j : Fin p → α) :
    entryProduct i j U⁻¹ = star (entryProduct j i U) := by
  simp [entryProduct, Matrix.star_apply]

theorem mixedMonomial_inv (U : UnitaryGroup α) (i j i' j' : Fin p → α) :
    mixedMonomial i j i' j' U⁻¹ = star (mixedMonomial j i j' i' U) := by
  simp only [mixedMonomial, entryProduct_inv, star_star, star_mul, mul_comm]

/-- Inversion invariance of Haar measure makes the moment matrix Hermitian. -/
theorem momentMatrix_conjTranspose : (momentMatrix α p)ᴴ = momentMatrix α p := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  change star (∫ U, mixedMonomial j i j' i' U ∂haar α) =
    ∫ U, mixedMonomial i j i' j' U ∂haar α
  have hc : star (∫ U, mixedMonomial j i j' i' U ∂haar α) =
      ∫ U, star (mixedMonomial j i j' i' U) ∂haar α :=
    (integral_conj (𝕜 := ℂ) (f := mixedMonomial j i j' i') (μ := haar α)).symm
  rw [hc]
  simp_rw [← mixedMonomial_inv]
  exact integral_inv_eq_self _ _

end Weingarten
