import Weingarten.Haar
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Order.Interval.Set.Infinite

/-!
# Polynomial identities on the unitary group

A complex polynomial in matrix entries that vanishes on the unitary group
vanishes on every matrix. The proof uses the spectral theorem, polynomial
uniqueness on a product of circles, then complexification of Hermitian matrices.
-/

set_option autoImplicit false

open scoped Matrix BigOperators
open Matrix MvPolynomial

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem circle_range_infinite : (Set.range ((↑) : Circle → ℂ)).Infinite := by
  have h : (Set.Ioc (-Real.pi) Real.pi).Infinite :=
    Set.Ioc_infinite (by linarith [Real.pi_pos])
  letI := h.to_subtype
  letI : Infinite Circle := Infinite.of_injective _ Circle.argEquiv.symm.injective
  exact @Set.infinite_range_of_injective Circle ℂ _ ((↑) : Circle → ℂ) Circle.coe_injective

private theorem eval_bind {ι κ : Type*} (f : ι → MvPolynomial κ ℂ)
    (p : MvPolynomial ι ℂ) (z : κ → ℂ) :
    eval z (bind₁ f p) = eval (fun i => eval z (f i)) p :=
  eval₂Hom_bind₁ (RingHom.id ℂ) z f p

/-- A polynomial identity on unitary matrices also holds on Hermitian matrices. -/
theorem polynomial_eq_zero_on_hermitian
    (p : MvPolynomial (α × α) ℂ)
    (hp : ∀ U : UnitaryGroup α, eval (fun ij => U ij.1 ij.2) p = 0)
    (H : Matrix α α ℂ) (hH : H.IsHermitian) :
    eval (fun ij => H ij.1 ij.2) p = 0 := by
  classical
  let U := hH.eigenvectorUnitary
  let f : α × α → MvPolynomial α ℂ :=
    fun ij => ∑ a, C (U ij.1 a * star (U ij.2 a)) * X a
  have hf (z : α → ℂ) (ij : α × α) :
      eval z (f ij) = (U.val * diagonal z * U.valᴴ) ij.1 ij.2 := by
    simp only [f, map_sum, map_mul, eval_C, eval_X]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hq : bind₁ f p = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range ((↑) : Circle → ℂ))
      (fun _ => circle_range_infinite)
    intro z hz
    have hz' : ∀ a, ∃ c : Circle, (c : ℂ) = z a := fun a => hz a (Set.mem_univ _)
    choose c hc using hz'
    let D : UnitaryGroup α := ⟨diagonal z, by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        change z i * star (z i) = 1
        rw [← hc i]
        change (c i : ℂ) * (starRingEnd ℂ) (c i : ℂ) = 1
        rw [← Circle.coe_inv_eq_conj]
        rw [Circle.coe_inv]
        exact mul_inv_cancel₀ (Circle.coe_ne_zero _)
      · simp [hij]⟩
    rw [eval_bind]
    simp_rw [hf]
    simpa only [map_zero] using hp (U * D * U⁻¹)
  have he := congr_arg (eval (fun a => (hH.eigenvalues a : ℂ))) hq
  rw [eval_bind, map_zero] at he
  simp_rw [hf] at he
  have hspec : H = U.val * diagonal (fun a => (hH.eigenvalues a : ℂ)) * U.valᴴ :=
    hH.spectral_theorem
  simpa only [← hspec] using he

/-- Unitary matrices are Zariski dense in all complex square matrices, stated as
the polynomial identity principle needed for Schur–Weyl duality. -/
theorem polynomial_eq_zero_of_unitary
    (p : MvPolynomial (α × α) ℂ)
    (hp : ∀ U : UnitaryGroup α, eval (fun ij => U ij.1 ij.2) p = 0)
    (M : Matrix α α ℂ) : eval (fun ij => M ij.1 ij.2) p = 0 := by
  let H := M + Mᴴ
  let K := Complex.I • (M - Mᴴ)
  have hH : H.IsHermitian := Matrix.isHermitian_add_transpose_self M
  have hK : K.IsHermitian := by
    change (Complex.I • (M - Mᴴ))ᴴ = Complex.I • (M - Mᴴ)
    simp [Matrix.conjTranspose_smul, sub_eq_add_neg, add_comm]
  let f : α × α → MvPolynomial Bool ℂ :=
    fun ij => X false * C (H ij.1 ij.2) + X true * C (K ij.1 ij.2)
  have hf (z : Bool → ℂ) (ij : α × α) :
      eval z (f ij) = (z false • H + z true • K) ij.1 ij.2 := by
    simp [f, Matrix.add_apply, Matrix.smul_apply]
  have hq : bind₁ f p = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro z hz
    obtain ⟨x, hx⟩ := hz false (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hz true (Set.mem_univ _)
    rw [eval_bind]
    simp_rw [hf]
    rw [map_zero]
    apply polynomial_eq_zero_on_hermitian p hp
    change (z false • H + z true • K)ᴴ = z false • H + z true • K
    rw [← hx, ← hy]
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH.eq, hK.eq]
  let z : Bool → ℂ := fun b => if b then -Complex.I / 2 else 1 / 2
  have he := congr_arg (eval z) hq
  rw [eval_bind, map_zero] at he
  simp_rw [hf] at he
  have hM : z false • H + z true • K = M := by
    ext i j
    simp only [z, Bool.false_eq_true, if_false, if_true, H, K, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    simp only [Complex.I_sq]
    ring
  simpa only [hM] using he

end

end Weingarten
