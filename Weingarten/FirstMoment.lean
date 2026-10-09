import Weingarten.Moments
import Weingarten.Symmetries

set_option autoImplicit false

/-! # The unitary Weingarten formula at moment order one, in every dimension -/

open MeasureTheory
open scoped BigOperators

namespace Weingarten

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integrable_entry_mul_conj (i j k l : α) :
    Integrable (fun U : UnitaryGroup α => U i j * star (U k l)) (haar α) := by
  have h (a b : α) : Continuous (fun U : UnitaryGroup α => U a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)
  exact ((h i j).mul (h k l).star).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_entry_mul_conj_eq_zero_of_row_ne (i j k l : α) (h : i ≠ k) :
    (∫ U : UnitaryGroup α, U i j * star (U k l) ∂haar α) = 0 := by
  have heq := integral_mul_left_eq_self (μ := haar α)
    (fun U : UnitaryGroup α => U i j * star (U k l)) (signUnitary i)
  simp only [signUnitary_mul_apply, ite_true, if_neg (Ne.symm h), one_mul,
    neg_mul] at heq
  rw [integral_neg] at heq
  exact neg_eq_self.mp heq

theorem integral_entry_mul_conj_eq_zero_of_column_ne (i j k l : α) (h : j ≠ l) :
    (∫ U : UnitaryGroup α, U i j * star (U k l) ∂haar α) = 0 := by
  have heq := integral_mul_right_eq_self (μ := haar α)
    (fun U : UnitaryGroup α => U i j * star (U k l)) (signUnitary j)
  simp only [mul_signUnitary_apply, ite_true, if_neg (Ne.symm h), mul_one,
    mul_neg_one, neg_mul] at heq
  rw [integral_neg] at heq
  exact neg_eq_self.mp heq

/-- All entries in a fixed column have the same mean squared absolute value. -/
theorem integral_entry_mul_conj_self_row (i k j : α) :
    (∫ U : UnitaryGroup α, U i j * star (U i j) ∂haar α) =
      ∫ U : UnitaryGroup α, U k j * star (U k j) ∂haar α := by
  have h := integral_mul_left_eq_self (μ := haar α)
    (fun U : UnitaryGroup α => U k j * star (U k j))
    (permutationUnitary (Equiv.swap i k))
  simpa using h

/-- The normalized second absolute moment of an entry is the reciprocal dimension. -/
theorem integral_entry_mul_conj_self (i j : α) :
    (∫ U : UnitaryGroup α, U i j * star (U i j) ∂haar α) =
      (Fintype.card α : ℂ)⁻¹ := by
  have hsum : (∑ k : α, ∫ U : UnitaryGroup α, U k j * star (U k j) ∂haar α) = 1 := by
    rw [← integral_finset_sum _ (fun k _ => integrable_entry_mul_conj k j k j)]
    have hpoint (U : UnitaryGroup α) : (∑ k, U k j * star (U k j)) = 1 := by
      simpa [mul_comm] using sum_conj_mul_column U j j
    simp_rw [hpoint]
    simp
  have heq (k : α) := integral_entry_mul_conj_self_row k i j
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hn : (Fintype.card α : ℂ) ≠ 0 := by
    have : Nonempty α := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using hsum

/-- The complete `p = 1` unitary integration formula. The presence of indices makes
the dimension positive; no nonemptiness assumption is silently added to `U(0)`. -/
theorem integral_entry_mul_conj (i j k l : α) :
    (∫ U : UnitaryGroup α, U i j * star (U k l) ∂haar α) =
      (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) /
        (Fintype.card α : ℂ) := by
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l
      simpa using integral_entry_mul_conj_self i j
    · rw [integral_entry_mul_conj_eq_zero_of_column_ne i j i l hj]
      simp [hj]
  · rw [integral_entry_mul_conj_eq_zero_of_row_ne i j k l hi]
    simp [hi]

end Weingarten
