import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # Words with equal multiplicities differ by a permutation of positions -/

set_option autoImplicit false

open scoped BigOperators

namespace Weingarten

noncomputable section

variable {ι β : Type*} [Fintype ι] [DecidableEq β]

/-- The multiplicity of each letter of a finite word. -/
def wordWeight (f : ι → β) : β →₀ ℕ := ∑ a, Finsupp.single (f a) 1

theorem wordWeight_apply (f : ι → β) (b : β) :
    wordWeight f b = Fintype.card {a // f a = b} := by
  classical
  simp [wordWeight, Finsupp.finset_sum_apply, Finsupp.single_apply, Fintype.card_subtype]

/-- This statement does not require the word to have distinct letters. -/
theorem exists_perm_of_wordWeight_eq (f g : ι → β) (h : wordWeight f = wordWeight g) :
    ∃ σ : Equiv.Perm ι, g = f ∘ σ := by
  classical
  have hc (b : β) : Fintype.card {a // f a = b} = Fintype.card {a // g a = b} := by
    rw [← wordWeight_apply f b, ← wordWeight_apply g b, h]
  let e (b : β) := Fintype.equivOfCardEq (hc b)
  let σ : Equiv.Perm ι := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g))
  have hg (a : ι) : g (σ a) = f a := (e (f a) ⟨a, rfl⟩).property
  refine ⟨σ.symm, ?_⟩
  funext a
  simpa only [Equiv.apply_symm_apply, Function.comp_apply] using hg (σ.symm a)

omit [DecidableEq β] in
theorem eval_monomial_wordWeight (f : ι → β) (z : β → ℂ) :
    MvPolynomial.eval z (MvPolynomial.monomial (wordWeight f) (1 : ℂ)) = ∏ a, z (f a) := by
  classical
  rw [wordWeight, MvPolynomial.monomial_sum_one, map_prod]
  apply Finset.prod_congr rfl
  intro a _
  simp [MvPolynomial.eval_monomial]

end

end Weingarten
