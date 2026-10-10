import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Complex.Basic

/-! # Cycle counts and the transposition length of permutations

Cycles are the equivalence classes of `SameCycle`, including singleton cycles.
The triangle inequality follows from dimensions of spaces of cycle-constant functions.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Weingarten

noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The set of cycles, including fixed points as singleton cycles. -/
abbrev PermCycles (σ : Equiv.Perm ι) := Quotient (Equiv.Perm.SameCycle.setoid σ)

/-- Number of cycles, including fixed points. -/
def cycleCount (σ : Equiv.Perm ι) : ℕ := Nat.card (PermCycles σ)

/-- The transposition length: the number of positions minus the number of cycles. -/
def permLength (σ : Equiv.Perm ι) : ℕ := Fintype.card ι - cycleCount σ

theorem eq_on_sameCycle {β : Type*} (σ : Equiv.Perm ι) (f : ι → β)
    (hf : ∀ a, f (σ a) = f a) {a b : ι} (h : σ.SameCycle a b) : f a = f b := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  symm
  induction n with
  | zero => rfl
  | succ n hn => simpa only [pow_succ', Equiv.Perm.mul_apply, hf] using hn

/-- Functions on cycles are exactly functions fixed by reindexing. -/
def cycleFunctionEquiv (σ : Equiv.Perm ι) (β : Type*) :
    (PermCycles σ → β) ≃ {f : ι → β // ∀ a, f (σ a) = f a} where
  toFun f := ⟨fun a => f (Quotient.mk _ a), fun a => congr_arg f
    (Quotient.sound (by exact (Equiv.Perm.SameCycle.refl σ a).apply_left))⟩
  invFun f := Quotient.lift f.val (fun _ _ h => eq_on_sameCycle σ f.val f.property h)
  left_inv f := by funext q; induction q using Quotient.inductionOn; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- Complex coordinate functions fixed by a permutation. -/
def cycleFunctions (σ : Equiv.Perm ι) : Submodule ℂ (ι → ℂ) where
  carrier := {f | ∀ a, f (σ a) = f a}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg a; simp [hf a, hg a]
  smul_mem' := by intro c f hf a; simp [hf a]

private def cycleFunctionLinearEquiv (σ : Equiv.Perm ι) :
    (PermCycles σ → ℂ) ≃ₗ[ℂ] cycleFunctions σ :=
  { cycleFunctionEquiv σ ℂ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem finrank_cycleFunctions (σ : Equiv.Perm ι) :
    Module.finrank ℂ (cycleFunctions σ) = cycleCount σ := by
  classical
  letI := Fintype.ofFinite (PermCycles σ)
  rw [← (cycleFunctionLinearEquiv σ).finrank_eq, Module.finrank_pi]
  exact Nat.card_eq_fintype_card.symm

theorem cycleCount_le (σ : Equiv.Perm ι) : cycleCount σ ≤ Fintype.card ι := by
  rw [← finrank_cycleFunctions]
  simpa using (cycleFunctions σ).finrank_le

omit [Fintype ι] in
@[simp] theorem cycleFunctions_one : cycleFunctions (1 : Equiv.Perm ι) = ⊤ := by
  ext f
  simp [cycleFunctions]

@[simp] theorem permLength_one : permLength (1 : Equiv.Perm ι) = 0 := by
  rw [permLength, ← finrank_cycleFunctions, cycleFunctions_one]
  simp

theorem permLength_le (σ : Equiv.Perm ι) : permLength σ ≤ Fintype.card ι :=
  Nat.sub_le _ _

/-- On a nonempty index type, the length is strictly less than its cardinality. -/
theorem permLength_lt [Nonempty ι] (σ : Equiv.Perm ι) :
    permLength σ < Fintype.card ι := by
  classical
  letI := Fintype.ofFinite (PermCycles σ)
  letI : Nonempty (PermCycles σ) := ⟨Quotient.mk _ (Classical.arbitrary ι)⟩
  have hc : 0 < cycleCount σ := by
    simpa [cycleCount, Nat.card_eq_fintype_card] using
      Fintype.card_pos (α := PermCycles σ)
  have hn := Fintype.card_pos (α := ι)
  unfold permLength
  omega

omit [Fintype ι] in
theorem cycleFunctions_inv (σ : Equiv.Perm ι) : cycleFunctions σ⁻¹ = cycleFunctions σ := by
  ext f
  constructor
  · intro hf a
    simpa using (hf (σ a)).symm
  · intro hf a
    simpa using (hf (σ⁻¹ a)).symm

@[simp] theorem permLength_inv (σ : Equiv.Perm ι) : permLength σ⁻¹ = permLength σ := by
  unfold permLength
  rw [← finrank_cycleFunctions, ← finrank_cycleFunctions, cycleFunctions_inv]

theorem permLength_mul_le (σ τ : Equiv.Perm ι) :
    permLength (σ * τ) ≤ permLength σ + permLength τ := by
  have hinf : cycleFunctions σ ⊓ cycleFunctions τ ≤ cycleFunctions (σ * τ) := by
    intro f hf a
    exact (hf.1 (τ a)).trans (hf.2 a)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (cycleFunctions σ) (cycleFunctions τ)
  have hsup := (cycleFunctions σ ⊔ cycleFunctions τ).finrank_le
  have hi := Submodule.finrank_mono hinf
  simp only [Module.finrank_pi, finrank_cycleFunctions] at hd hsup hi
  have hs := cycleCount_le σ
  have ht := cycleCount_le τ
  have hst := cycleCount_le (σ * τ)
  unfold permLength
  omega

theorem permLength_eq_zero_iff (σ : Equiv.Perm ι) : permLength σ = 0 ↔ σ = 1 := by
  classical
  constructor
  · intro h
    have hc : Module.finrank ℂ (cycleFunctions σ) = Fintype.card ι := by
      rw [finrank_cycleFunctions]
      have := cycleCount_le σ
      unfold permLength at h
      omega
    have htop : cycleFunctions σ = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hc)
    apply Equiv.ext
    intro a
    have hf : (fun b => if b = a then (1 : ℂ) else 0) ∈ cycleFunctions σ := by rw [htop]; trivial
    have ha := hf a
    simpa using ha
  · rintro rfl
    exact permLength_one

theorem permLength_triangle (σ ρ τ : Equiv.Perm ι) :
    permLength (σ⁻¹ * τ) ≤ permLength (σ⁻¹ * ρ) + permLength (ρ⁻¹ * τ) := by
  simpa [mul_assoc] using permLength_mul_le (σ⁻¹ * ρ) (ρ⁻¹ * τ)

end
end Weingarten
