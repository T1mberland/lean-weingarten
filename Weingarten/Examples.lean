import Weingarten
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.NormNum

/-! # Checked examples of the public API -/

set_option autoImplicit false

open Weingarten MeasureTheory
open scoped Matrix ComplexOrder

-- Every entry of a Haar unitary of size n+1 has mean squared modulus 1/(n+1).
example (n : ℕ) (i j : Fin (n + 1)) :
    (∫ U : UnitaryGroup (Fin (n + 1)), U i j * star (U i j) ∂haar (Fin (n + 1))) =
      (n + 1 : ℂ)⁻¹ := by
  simpa using integral_entry_mul_conj_self i j

-- Distinct rows give zero, even if the columns agree.
example : (∫ U : UnitaryGroup (Fin 2), U 0 0 * star (U 1 0) ∂haar (Fin 2)) = 0 := by
  exact integral_entry_mul_conj_eq_zero_of_row_ne 0 0 1 0 (by decide)

-- A concrete diagonal second moment.
example : (∫ U : UnitaryGroup (Fin 3), U 0 1 * star (U 0 1) ∂haar (Fin 3)) = 1 / 3 := by
  rw [integral_entry_mul_conj_self]
  norm_num

-- Odd total degree vanishes in arbitrary dimension.
example {n : ℕ} (i j : Fin 2 → Fin n) (i' j' : Fin 1 → Fin n) :
    mixedMoment i j i' j' = 0 :=
  mixedMoment_eq_zero_of_odd i j i' j' (by decide)

-- Arbitrarily high balanced moments of U(1).
example (p : ℕ) (i j i' j' : Fin p → Fin 1) : mixedMoment i j i' j' = 1 :=
  mixedMoment_eq_one_of_unique i j i' j'

-- Stable-range coefficients are the ordinary inverse of the Gram matrix.
example {p n : ℕ} (h : p ≤ n) :
    weingartenMatrix (Fin p) (Fin n) =
      (gramMatrix (ι := Fin p) (α := Fin n))⁻¹ :=
  weingartenMatrix_eq_inv (Fin.castLEEmb h)

-- No stable-range restriction is needed for the generalized-inverse equation.
example :
    gramMatrix (ι := Fin 3) (α := Fin 2) * weingartenMatrix (Fin 3) (Fin 2) *
      gramMatrix (ι := Fin 3) (α := Fin 2) = gramMatrix (ι := Fin 3) (α := Fin 2) :=
  gram_weingarten_gram _ _
