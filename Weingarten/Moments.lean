import Weingarten.Haar
import Mathlib.Tactic.FunProp

set_option autoImplicit false

/-! # Mixed moments of Haar unitary matrices -/

open scoped BigOperators
open MeasureTheory

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A matrix coefficient of a tensor power, written without tensor-product infrastructure. -/
def entryProduct {p : ℕ} (i j : Fin p → α) (U : UnitaryGroup α) : ℂ :=
  ∏ a, U (i a) (j a)

/-- A mixed monomial with `p` entries and `q` conjugate entries. -/
def mixedMonomial {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α)
    (U : UnitaryGroup α) : ℂ :=
  entryProduct i j U * star (entryProduct i' j' U)

/-- The genuine Bochner integral against normalized Haar measure. -/
def mixedMoment {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α) : ℂ :=
  ∫ U, mixedMonomial i j i' j' U ∂haar α

theorem continuous_entryProduct {p : ℕ} (i j : Fin p → α) :
    Continuous (entryProduct i j) := by
  unfold entryProduct
  apply continuous_finset_prod
  intro a _
  exact (continuous_apply (j a)).comp ((continuous_apply (i a)).comp continuous_subtype_val)

theorem continuous_mixedMonomial {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α) :
    Continuous (mixedMonomial i j i' j') :=
  (continuous_entryProduct i j).mul (continuous_entryProduct i' j').star

/-- In particular these moments do not rely on the default value of a nonintegrable integral. -/
theorem integrable_mixedMonomial {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α) :
    Integrable (mixedMonomial i j i' j') (haar α) :=
  (continuous_mixedMonomial i j i' j').integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[simp] theorem mixedMoment_zero (i j i' j' : Fin 0 → α) :
    mixedMoment i j i' j' = 1 := by
  simp [mixedMoment, mixedMonomial, entryProduct]

/-- A balanced moment matrix, with each index a pair of words. -/
def momentMatrix (α : Type*) [Fintype α] [DecidableEq α] (p : ℕ) :
    Matrix ((Fin p → α) × (Fin p → α)) ((Fin p → α) × (Fin p → α)) ℂ :=
  fun r c => mixedMoment r.1 c.1 r.2 c.2

/-- Negating a unitary matrix multiplies a tensor coefficient by the expected parity. -/
theorem entryProduct_neg {p : ℕ} (i j : Fin p → α) (U : UnitaryGroup α) :
    entryProduct i j (-U) = (-1 : ℂ) ^ p * entryProduct i j U := by
  change (∏ a, -(U (i a) (j a))) = _
  simp [Finset.prod_neg, entryProduct]

theorem mixedMonomial_neg {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α)
    (U : UnitaryGroup α) :
    mixedMonomial i j i' j' (-U) = (-1 : ℂ) ^ (p + q) * mixedMonomial i j i' j' U := by
  simp only [mixedMonomial, entryProduct_neg, star_mul, star_pow, star_neg, star_one, pow_add]
  ring

/-- Every mixed moment of odd total degree vanishes, in every matrix dimension. -/
theorem mixedMoment_eq_zero_of_odd {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α)
    (h : Odd (p + q)) : mixedMoment i j i' j' = 0 := by
  have heq := integral_mul_left_eq_self (μ := haar α)
    (mixedMonomial i j i' j') (-1 : UnitaryGroup α)
  have hneg : ∀ U : UnitaryGroup α,
      mixedMonomial i j i' j' ((-1) * U) = -mixedMonomial i j i' j' U := by
    intro U
    rw [neg_one_mul, mixedMonomial_neg, h.neg_one_pow, neg_one_mul]
  simp_rw [hneg] at heq
  rw [integral_neg] at heq
  change -mixedMoment i j i' j' = mixedMoment i j i' j' at heq
  exact neg_eq_self.mp heq

/-- For a one-dimensional unitary group, every balanced monomial is identically one. -/
theorem mixedMonomial_eq_one_of_unique [Unique α] {p : ℕ}
    (i j i' j' : Fin p → α) (U : UnitaryGroup α) :
    mixedMonomial i j i' j' U = 1 := by
  have h : U default default * star (U default default) = 1 := by
    simpa using sum_row_mul_conj U default default
  have hi : i = fun _ => default := Subsingleton.elim _ _
  have hj : j = fun _ => default := Subsingleton.elim _ _
  have hi' : i' = fun _ => default := Subsingleton.elim _ _
  have hj' : j' = fun _ => default := Subsingleton.elim _ _
  change U default default * (starRingEnd ℂ) (U default default) = 1 at h
  simp [mixedMonomial, entryProduct, hi, hj, hi', hj', ← mul_pow, h]

/-- All balanced moments of Haar `U(1)`, for arbitrary moment order. -/
theorem mixedMoment_eq_one_of_unique [Unique α] {p : ℕ}
    (i j i' j' : Fin p → α) : mixedMoment i j i' j' = 1 := by
  simp [mixedMoment, mixedMonomial_eq_one_of_unique]

end

end Weingarten
