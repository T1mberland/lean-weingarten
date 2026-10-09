import Weingarten.Moments
import Weingarten.UnitaryPolynomial

/-! # All unbalanced Haar moments vanish -/

set_option autoImplicit false

open scoped BigOperators Matrix
open MeasureTheory Matrix

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A scalar phase acting simultaneously on all rows. -/
def phaseUnitary (z : ℂ) (hz : z * star z = 1) : UnitaryGroup α :=
  ⟨diagonal (fun _ => z), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simpa using hz
    · simp [h]⟩

theorem entryProduct_phase {p : ℕ} (i j : Fin p → α) (U : UnitaryGroup α)
    (z : ℂ) (hz : z * star z = 1) :
    entryProduct i j (phaseUnitary z hz * U) = z ^ p * entryProduct i j U := by
  simp [entryProduct, phaseUnitary, Matrix.diagonal_mul, Finset.prod_mul_distrib]

theorem mixedMonomial_phase {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α)
    (U : UnitaryGroup α) (z : ℂ) (hz : z * star z = 1) :
    mixedMonomial i j i' j' (phaseUnitary z hz * U) =
      (z ^ p * star (z ^ q)) * mixedMonomial i j i' j' U := by
  simp only [mixedMonomial, entryProduct_phase, StarMul.star_mul]
  ring

/-- Unequal numbers of entries and conjugate entries have zero Haar integral.
Together with `integral_unitary_weingarten`, this treats every mixed monomial. -/
theorem mixedMoment_eq_zero_of_ne {p q : ℕ} (i j : Fin p → α) (i' j' : Fin q → α)
    (hpq : p ≠ q) : mixedMoment i j i' j' = 0 := by
  by_contra hm
  have hphase (z : ℂ) (hz : z * star z = 1) : z ^ p = z ^ q := by
    have heq := integral_mul_left_eq_self (μ := haar α)
      (mixedMonomial i j i' j') (phaseUnitary z hz)
    simp_rw [mixedMonomial_phase] at heq
    rw [integral_const_mul] at heq
    change (z ^ p * star (z ^ q)) * mixedMoment i j i' j' = mixedMoment i j i' j' at heq
    have he : z ^ p * star (z ^ q) = 1 := (mul_right_cancel₀ hm) (by simpa using heq)
    have hzz : star (z ^ q) * z ^ q = 1 := by
      rw [star_pow, ← mul_pow, mul_comm, hz, one_pow]
    calc
      z ^ p = z ^ p * (star (z ^ q) * z ^ q) := by rw [hzz, mul_one]
      _ = (z ^ p * star (z ^ q)) * z ^ q := (mul_assoc _ _ _).symm
      _ = z ^ q := by rw [he, one_mul]
  let Q : MvPolynomial (Fin 1 × Fin 1) ℂ :=
    MvPolynomial.X (0, 0) ^ p - MvPolynomial.X (0, 0) ^ q
  have hQ : ∀ U : UnitaryGroup (Fin 1),
      MvPolynomial.eval (fun ab => U ab.1 ab.2) Q = 0 := by
    intro U
    have hz : U 0 0 * star (U 0 0) = 1 := by simpa using sum_row_mul_conj U 0 0
    simpa [Q] using sub_eq_zero.mpr (hphase (U 0 0) hz)
  have h := polynomial_eq_zero_of_unitary Q hQ (fun _ _ => 2)
  have he : (2 : ℂ) ^ p = 2 ^ q := by simpa [Q, sub_eq_zero] using h
  have he' : (2 : ℝ) ^ p = 2 ^ q := by exact_mod_cast he
  exact hpq ((pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective he')

end

end Weingarten
