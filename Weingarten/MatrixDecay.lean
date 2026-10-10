import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Decay of inverse entries for matrices indexed by a finite metric

A weighted maximum argument gives a deliberately coarse constant, avoiding
asymptotic series or an assumption of convergence of a formal inverse.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Weingarten

private theorem weighted_power_le (d L : ℝ) (hL : 1 ≤ L) (hd : L ≤ d)
    (a b c r : ℕ) (hab : a ≤ c + b) (hc : c ≤ r) (hc0 : 1 ≤ c) :
    (d / L) ^ a * d ^ (r - c) ≤ (d ^ r / L) * (d / L) ^ b := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdp : 0 < d := hLp.trans_le hd
  have hz : 1 ≤ d / L := (one_le_div hLp).mpr hd
  have hpow : L ≤ L ^ c := by simpa using pow_le_pow_right₀ hL hc0
  calc
    (d / L) ^ a * d ^ (r - c) ≤ (d / L) ^ (c + b) * d ^ (r - c) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz hab) (pow_nonneg hdp.le _)
    _ = (d ^ r / L ^ c) * (d / L) ^ b := by
      rw [pow_add]
      have he : (d / L) ^ c * d ^ (r - c) = d ^ r / L ^ c := by
        rw [div_pow, div_mul_eq_mul_div, ← pow_add, Nat.add_sub_of_le hc]
      calc
        _ = ((d / L) ^ c * d ^ (r - c)) * (d / L) ^ b := by ring
        _ = _ := by rw [he]
    _ ≤ (d ^ r / L) * (d / L) ^ b :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (pow_nonneg hdp.le _) hLp hpow)
        (pow_nonneg (div_nonneg hdp.le hLp.le) _)

/-- A finite-metric inverse bound. The hypothesis on entry norms includes the
unit diagonal after scaling by `d^r`. -/
theorem matrix_inverse_entry_decay {n : Type*} [Fintype n] [DecidableEq n]
    (ell : n → n → ℕ) (r : ℕ)
    (hell0 : ∀ i, ell i i = 0) (hellpos : ∀ i k, i ≠ k → 1 ≤ ell i k)
    (hellle : ∀ i k, ell i k ≤ r)
    (htriangle : ∀ i k j, ell i j ≤ ell i k + ell k j)
    (d : ℝ) (hd : 2 * (Fintype.card n : ℝ) ≤ d)
    (G W : Matrix n n ℂ) (hGW : G * W = 1)
    (hG : ∀ i k, ‖G i k‖ = d ^ (r - ell i k)) (i j : n) :
    d ^ (r + ell i j) * ‖W i j‖ ≤ 2 * (2 * (Fintype.card n : ℝ)) ^ r := by
  classical
  letI : Nonempty n := ⟨j⟩
  let L : ℝ := 2 * Fintype.card n
  have hn : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdp : 0 < d := hLp.trans_le hd
  have hz : 1 ≤ d / L := (one_le_div hLp).mpr hd
  let v : n → ℝ := fun a => (d / L) ^ ell a j * ‖W a j‖
  have hv : ∀ a, 0 ≤ v a := fun a => mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _)
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ v ⟨j, Finset.mem_univ j⟩
  have hmax (k : n) : v k ≤ v a := ha k (Finset.mem_univ k)
  have hrow : G a a * W a j = (1 : Matrix n n ℂ) a j -
      ∑ k ∈ Finset.univ.erase a, G a k * W k j := by
    have he := congr_fun (congr_fun hGW a) j
    rw [Matrix.mul_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)] at he
    linear_combination he
  have hnorm : d ^ r * ‖W a j‖ ≤ ‖(1 : Matrix n n ℂ) a j‖ +
      ∑ k ∈ Finset.univ.erase a, d ^ (r - ell a k) * ‖W k j‖ := by
    calc
      _ = ‖G a a * W a j‖ := by rw [norm_mul, hG, hell0, Nat.sub_zero]
      _ ≤ _ := by
        rw [hrow]
        have hs : ‖∑ k ∈ Finset.univ.erase a, G a k * W k j‖ ≤
            ∑ k ∈ Finset.univ.erase a, d ^ (r - ell a k) * ‖W k j‖ := by
          simpa only [norm_mul, hG] using
            norm_sum_le (Finset.univ.erase a) (fun k => G a k * W k j)
        exact (norm_sub_le _ _).trans (add_le_add_right hs _)
  have hdelta : (d / L) ^ ell a j * ‖(1 : Matrix n n ℂ) a j‖ ≤ 1 := by
    by_cases h : a = j
    · subst a; simp [hell0]
    · simp [h]
  have hweighted : d ^ r * v a ≤ 1 + (d ^ r / L) * ∑ k ∈ Finset.univ.erase a, v k := by
    calc
      d ^ r * v a = (d / L) ^ ell a j * (d ^ r * ‖W a j‖) := by dsimp [v]; ring
      _ ≤ (d / L) ^ ell a j * (‖(1 : Matrix n n ℂ) a j‖ +
          ∑ k ∈ Finset.univ.erase a, d ^ (r - ell a k) * ‖W k j‖) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by positivity) _)
      _ ≤ 1 + (d ^ r / L) * ∑ k ∈ Finset.univ.erase a, v k := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        apply add_le_add hdelta
        apply Finset.sum_le_sum
        intro k hk
        have hak : a ≠ k := (Finset.mem_erase.mp hk).1.symm
        have ht := weighted_power_le d L hL hd (ell a j) (ell k j) (ell a k) r
          (htriangle a k j) (hellle a k) (hellpos a k hak)
        simpa [v, mul_assoc] using mul_le_mul_of_nonneg_right ht (norm_nonneg (W k j))
  have hsum : (∑ k ∈ Finset.univ.erase a, v k) ≤ (Fintype.card n : ℝ) * v a := by
    calc
      _ ≤ ∑ k : n, v k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun k _ _ => hv k)
      _ ≤ ∑ _k : n, v a := Finset.sum_le_sum (fun k _ => hmax k)
      _ = _ := by simp
  have hbound : d ^ r * v a ≤ 2 := by
    have h := hweighted.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hsum (show 0 ≤ d ^ r / L by positivity)) 1)
    have he : (d ^ r / L) * ((Fintype.card n : ℝ) * v a) = (d ^ r * v a) / 2 := by
      dsimp [L]
      field_simp
    rw [he] at h
    linarith
  have hi : d ^ r * v i ≤ 2 :=
    (mul_le_mul_of_nonneg_left (hmax i) (pow_nonneg hdp.le _)).trans hbound
  calc
    d ^ (r + ell i j) * ‖W i j‖ = L ^ ell i j * (d ^ r * v i) := by
      dsimp [v]
      rw [pow_add, div_pow]
      field_simp
    _ ≤ L ^ ell i j * 2 := mul_le_mul_of_nonneg_left hi (pow_nonneg hLp.le _)
    _ ≤ 2 * L ^ r := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (hellle i j)) (by norm_num)

end Weingarten
