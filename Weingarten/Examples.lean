import Weingarten
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.NormNum

/-! # Checked examples of the public API -/

set_option autoImplicit false

open Weingarten MeasureTheory
open scoped BigOperators Matrix ComplexOrder

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

-- The full formula, for arbitrary positive dimension and arbitrary moment order.
example {d k : ℕ} (i j i' j' : Fin k → Fin (d + 1)) :
    (∫ U : UnitaryGroup (Fin (d + 1)),
      (∏ a, U (i a) (j a)) * star (∏ a, U (i' a) (j' a)) ∂haar (Fin (d + 1))) =
      ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
        pairing σ i i' * weingartenMatrix (Fin k) (Fin (d + 1)) σ τ * pairing τ j j' :=
  integral_unitary_weingarten i j i' j'

-- Actual integration in the singular regime d = 2 < k = 3, with no spanning assumption.
example (i j i' j' : Fin 3 → Fin 2) :
    mixedMoment i j i' j' =
      ∑ σ : Equiv.Perm (Fin 3), ∑ τ : Equiv.Perm (Fin 3),
        pairing σ i i' * weingartenMatrix (Fin 3) (Fin 2) σ τ * pairing τ j j' :=
  mixedMoment_eq_weingarten i j i' j'

-- Unequal degrees vanish even when their sum is even.
example {d : ℕ} (i j : Fin 4 → Fin d) (i' j' : Fin 2 → Fin d) :
    mixedMoment i j i' j' = 0 :=
  mixedMoment_eq_zero_of_ne i j i' j' (by decide)

-- The previously missing factorization is now a theorem in all dimensions and orders.
example (d k : ℕ) :
    ∃ B, momentMatrix (Fin d) k = diagramMatrix * B :=
  momentMatrix_factorization
