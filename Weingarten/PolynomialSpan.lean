import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! # Spanning finite families of monomial evaluations -/

set_option autoImplicit false

open scoped BigOperators
open MvPolynomial

namespace Weingarten

noncomputable section

private theorem functional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Module.Dual ℂ (ι → ℂ)) (v : ι → ℂ) :
    φ v = ∑ i, v i * φ (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Pi.single i (v i) : ι → ℂ) = v i • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    funext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [hi, map_smul, smul_eq_mul]

/-- Evaluation vectors of monomials span every vector constant on equal-exponent
fibers. Repeated exponents are allowed; this is the form needed in the singular
Schur–Weyl regime. -/
theorem mem_span_monomial_evaluations
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → κ →₀ ℕ) (v : ι → ℂ)
    (hv : ∀ i j, w i = w j → v i = v j) :
    v ∈ Submodule.span ℂ (Set.range (fun z : κ → ℂ =>
      fun i => eval z (monomial (w i) (1 : ℂ)))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun z : κ → ℂ =>
    fun i => eval z (monomial (w i) (1 : ℂ))))
  have hind (d : κ →₀ ℕ) : (fun i => if w i = d then (1 : ℂ) else 0) ∈ S := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    let Q : MvPolynomial κ ℂ := ∑ i, monomial (w i) (φ (Pi.single i 1))
    have hQ : Q = 0 := by
      apply MvPolynomial.funext
      intro z
      rw [map_zero]
      have hzero : φ (fun i => eval z (monomial (w i) (1 : ℂ))) = 0 :=
        hφ _ (Submodule.subset_span ⟨z, rfl⟩)
      rw [functional_eq_sum] at hzero
      simpa [Q, eval_monomial, mul_comm] using hzero
    have hc := congr_arg (coeff d) hQ
    rw [functional_eq_sum]
    simpa [Q, coeff_sum, coeff_monomial, eq_comm] using hc
  have hex : ∀ d ∈ Finset.univ.image w, ∃ i, w i = d := by
    intro d hd
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hd
    exact ⟨i, hi⟩
  choose a ha using hex
  have heq : v = ∑ d : {d // d ∈ Finset.univ.image w},
      v (a d.1 d.2) • (fun i => if w i = d.1 then (1 : ℂ) else 0) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    let d : {d // d ∈ Finset.univ.image w} := ⟨w i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
    rw [Finset.sum_eq_single d]
    · simp only [d, if_true, mul_one]
      exact hv i (a (w i) d.2) (ha (w i) d.2).symm
    · intro b _ hb
      have hbi : w i ≠ b.1 := by
        intro h
        apply hb
        exact Subtype.ext h.symm
      simp [hbi]
    · simp
  rw [heq]
  exact Submodule.sum_mem S (fun d _ => S.smul_mem _ (hind d.1))

end

end Weingarten
