import Weingarten.GeneralizedInverse
import Weingarten.GramCycles
import Weingarten.MatrixDecay
import Mathlib.Analysis.Asymptotics.Defs

/-! # Uniform decay of unitary Weingarten coefficients

For fixed order `r`, the constant is uniform over permutations and all positive
integer dimensions, including the singular range. An explicit coarse constant
works for `d ≥ 2 * r!`; a finite correction covers the smaller dimensions.
-/

set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder
namespace Weingarten
noncomputable section

/-- The one-permutation Weingarten coefficient, taken from the identity row of
our standard Gram pseudoinverse. -/
def weingarten {r : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin r)) : ℂ :=
  weingartenMatrix (Fin r) (Fin d) 1 σ

/-- An explicit, nonoptimal constant for dimensions at least `2 * r!`. -/
def largeDimensionBound (r : ℕ) : ℝ := 2 * (2 * (r.factorial : ℝ)) ^ r

/-- The exponent detects the relative permutation, not just the moment order. -/
theorem weingartenMatrix_scaled_bound {r d : ℕ} (hd : 2 * r.factorial ≤ d)
    (σ τ : Equiv.Perm (Fin r)) :
    (d : ℝ) ^ (r + permLength (τ * σ⁻¹)) * ‖weingartenMatrix (Fin r) (Fin d) σ τ‖ ≤
      largeDimensionBound r := by
  have hrd : r ≤ d := (Nat.self_le_factorial r).trans (by omega)
  let e : Fin r ↪ Fin d := Fin.castLEEmb hrd
  have hGW : gramMatrix (ι := Fin r) (α := Fin d) * weingartenMatrix (Fin r) (Fin d) = 1 := by
    rw [weingartenMatrix_eq_inv e]
    exact Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (gramMatrix_posDef e).isUnit)
  apply (matrix_inverse_entry_decay (fun a b => permLength (b * a⁻¹)) r
    (by intro a; simp)
    (by
      intro a b hab
      apply Nat.one_le_iff_ne_zero.mpr
      change permLength (b * a⁻¹) ≠ 0
      exact (permLength_eq_zero_iff _).not.mpr (by simpa only [mul_inv_eq_one] using hab.symm))
    (by intro a b; simpa using permLength_le (b * a⁻¹))
    (by
      intro a b c
      simpa [mul_assoc, Nat.add_comm] using permLength_mul_le (c * b⁻¹) (b * a⁻¹))
    (d : ℝ) (by exact_mod_cast (by simpa [Fintype.card_perm] using hd :
      2 * Fintype.card (Equiv.Perm (Fin r)) ≤ d))
    _ _ hGW (by
      intro a b
      simp [gramMatrix_eq_pow_permLength]) σ τ).trans_eq
  simp [largeDimensionBound, Fintype.card_perm]

/-- Explicit decay for sufficiently large dimension, uniform in the permutation. -/
theorem weingarten_scaled_bound_large {r d : ℕ} (hd : 2 * r.factorial ≤ d)
    (σ : Equiv.Perm (Fin r)) :
    (d : ℝ) ^ (r + permLength σ) * ‖weingarten d σ‖ ≤ largeDimensionBound r := by
  simpa [weingarten] using weingartenMatrix_scaled_bound hd 1 σ

/-- An explicit coarse constant suffices above the displayed dimension threshold. -/
theorem norm_weingarten_le_large {r d : ℕ} (hd : 2 * r.factorial ≤ d)
    (σ : Equiv.Perm (Fin r)) :
    ‖weingarten d σ‖ ≤ largeDimensionBound r / (d : ℝ) ^ (r + permLength σ) := by
  have hdp : 0 < d := (Nat.mul_pos (by decide) (Nat.factorial_pos r)).trans_le hd
  apply (le_div_iff₀ (pow_pos (by exact_mod_cast hdp : (0 : ℝ) < d) _)).mpr
  simpa [mul_comm] using weingarten_scaled_bound_large hd σ

/-- A constant depending only on the order. The finite sum includes all small
positive dimensions (and harmlessly dimension zero), using the genuine
pseudoinverse coefficients there. -/
def weingartenBound (r : ℕ) : ℝ := largeDimensionBound r +
  ∑ d ∈ Finset.range (2 * r.factorial), ∑ σ : Equiv.Perm (Fin r),
    (d : ℝ) ^ (r + permLength σ) * ‖weingarten d σ‖

theorem largeDimensionBound_pos (r : ℕ) : 0 < largeDimensionBound r := by
  unfold largeDimensionBound
  positivity

theorem largeDimensionBound_le (r : ℕ) : largeDimensionBound r ≤ weingartenBound r := by
  unfold weingartenBound
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _))))

theorem weingartenBound_pos (r : ℕ) : 0 < weingartenBound r :=
  (largeDimensionBound_pos r).trans_le (largeDimensionBound_le r)

/-- The polynomially rescaled coefficients are bounded for every dimension. -/
theorem weingarten_scaled_bound {r : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin r)) :
    (d : ℝ) ^ (r + permLength σ) * ‖weingarten d σ‖ ≤ weingartenBound r := by
  by_cases hd : 2 * r.factorial ≤ d
  · exact (weingarten_scaled_bound_large hd σ).trans (largeDimensionBound_le r)
  · have hnonneg (n : ℕ) (τ : Equiv.Perm (Fin r)) :
        0 ≤ (n : ℝ) ^ (r + permLength τ) * ‖weingarten n τ‖ := by positivity
    have hσ := Finset.single_le_sum (fun τ _ => hnonneg d τ) (Finset.mem_univ σ)
    have hdmem : d ∈ Finset.range (2 * r.factorial) := Finset.mem_range.mpr (by omega)
    have hsum : (∑ τ : Equiv.Perm (Fin r),
        (d : ℝ) ^ (r + permLength τ) * ‖weingarten d τ‖) ≤
        ∑ n ∈ Finset.range (2 * r.factorial), ∑ τ : Equiv.Perm (Fin r),
          (n : ℝ) ^ (r + permLength τ) * ‖weingarten n τ‖ :=
      Finset.single_le_sum
        (fun n _ => Finset.sum_nonneg (fun τ _ => hnonneg n τ)) hdmem
    exact (hσ.trans hsum).trans (le_add_of_nonneg_left (largeDimensionBound_pos r).le)

/-- **Uniform Weingarten decay**: `|Wg_d(σ)| ≤ C_r / d^(r+|σ|)` for every
positive dimension, including singular Gram matrices. -/
theorem norm_weingarten_le {r : ℕ} (d : ℕ) (hd : 0 < d) (σ : Equiv.Perm (Fin r)) :
    ‖weingarten d σ‖ ≤ weingartenBound r / (d : ℝ) ^ (r + permLength σ) := by
  have hp : 0 < (d : ℝ) ^ (r + permLength σ) := pow_pos (by exact_mod_cast hd) _
  apply (le_div_iff₀ hp).mpr
  simpa [mul_comm] using weingarten_scaled_bound d σ

/-- The bound with the constant quantified before both dimension and permutation. -/
theorem exists_weingarten_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → ∀ σ : Equiv.Perm (Fin r),
      ‖weingarten d σ‖ ≤ C / (d : ℝ) ^ (r + permLength σ) :=
  ⟨weingartenBound r, weingartenBound_pos r, norm_weingarten_le⟩

/-- The usual large-dimension big-O statement, with the permutation held fixed. -/
theorem weingarten_isBigO {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    (fun d : ℕ => weingarten d σ) =O[Filter.atTop]
      (fun d : ℕ => ((d : ℝ) ^ (r + permLength σ))⁻¹) := by
  apply Asymptotics.IsBigO.of_bound (weingartenBound r)
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  simpa [div_eq_mul_inv] using norm_weingarten_le d (by omega) σ

end
end Weingarten
