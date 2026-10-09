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

-- Re-derive the order-one formula through the general theorem and its coefficient.
example {α : Type*} [Fintype α] [DecidableEq α] (i j i' j' : α) :
    (∫ U : UnitaryGroup α, U i j * star (U i' j') ∂haar α) =
      (if i = i' then (1 : ℂ) else 0) * (if j = j' then (1 : ℂ) else 0) /
        (Fintype.card α : ℂ) := by
  letI : Nonempty α := ⟨i⟩
  have h := integral_unitary_weingarten (fun _ : Fin 1 => i) (fun _ => j)
    (fun _ => i') (fun _ => j')
  simpa [weingartenMatrix_fin_one, pairing, Function.comp_def, funext_iff, eq_comm,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

-- Fourth absolute moment in U(2), obtained from the general formula.
example : (∫ U : UnitaryGroup (Fin 2),
    (U 0 0 * U 0 0) * star (U 0 0 * U 0 0) ∂haar (Fin 2)) = 1 / 3 := by
  have h := integral_unitary_two (α := Fin 2) (by decide)
    ![0, 0] ![0, 0] ![0, 0] ![0, 0]
  norm_num [pairing, funext_iff, Fin.forall_fin_two, Function.comp_def,
    Fin.prod_univ_two] at h
  simpa using h

-- A negative fourth mixed moment tests the off-diagonal coefficient and index convention.
example : (∫ U : UnitaryGroup (Fin 2),
    (U 0 0 * U 1 1) * star (U 0 1 * U 1 0) ∂haar (Fin 2)) = -1 / 6 := by
  have h := integral_unitary_two (α := Fin 2) (by decide)
    ![0, 1] ![0, 1] ![0, 1] ![1, 0]
  norm_num [pairing, funext_iff, Fin.forall_fin_two, Function.comp_def,
    Fin.prod_univ_two] at h
  simpa [div_eq_mul_inv] using h

-- In the singular case each coefficient is 1/4, not an ordinary inverse entry.
example (σ τ : Equiv.Perm (Fin 2)) :
    weingartenMatrix (Fin 2) (Fin 1) σ τ = 1 / 4 :=
  weingartenMatrix_one_two σ τ

example : (∫ U : UnitaryGroup (Fin 1),
    (U 0 0 * U 0 0) * star (U 0 0 * U 0 0) ∂haar (Fin 1)) = 1 := by
  simpa [Fin.prod_univ_two] using integral_one_two ![0, 0] ![0, 0] ![0, 0] ![0, 0]

-- Even dimension zero has an order-zero coefficient equal to one.
example (σ τ : Equiv.Perm (Fin 0)) : weingartenMatrix (Fin 0) (Fin 0) σ τ = 1 :=
  weingartenMatrix_fin_zero σ τ

example (i j i' j' : Fin 0 → Fin 0) : mixedMoment i j i' j' = 1 := by
  rw [mixedMoment_eq_weingarten]
  simp [weingartenMatrix_fin_zero, pairing, funext_iff]
