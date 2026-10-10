import Weingarten.Permutation
import Weingarten.PermutationLength

/-! # The standard cycle-count formula for the permutation Gram matrix -/

set_option autoImplicit false
open scoped BigOperators Matrix
namespace Weingarten

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- A Gram entry is `d` to the number of cycles of the relative permutation,
with fixed points counted as cycles. -/
theorem gramMatrix_eq_pow_cycleCount (σ τ : Equiv.Perm ι) :
    gramMatrix (α := α) σ τ = (Fintype.card α : ℂ) ^ cycleCount (τ * σ⁻¹) := by
  classical
  let ρ := τ * σ⁻¹
  letI := Fintype.ofFinite (PermCycles ρ)
  have he (f : ι → α) : f ∘ σ = f ∘ τ ↔ ∀ a, f (ρ a) = f a := by
    constructor
    · intro h a
      simpa [ρ] using (congr_fun h (σ⁻¹ a)).symm
    · intro h
      funext a
      simpa [ρ] using (h (σ a)).symm
  rw [gramMatrix_apply]
  simp_rw [he]
  have hc := Fintype.card_congr (cycleFunctionEquiv ρ α)
  have hcard : Fintype.card {f : ι → α // ∀ a, f (ρ a) = f a} =
      Fintype.card α ^ cycleCount ρ := by
    rw [← hc, Fintype.card_fun]
    simp [cycleCount, Nat.card_eq_fintype_card]
  rw [← Nat.cast_pow, ← hcard]
  simp [Fintype.card_subtype]

/-- The same Gram entry written in terms of the transposition length. -/
theorem gramMatrix_eq_pow_permLength (σ τ : Equiv.Perm ι) :
    gramMatrix (α := α) σ τ =
      (Fintype.card α : ℂ) ^ (Fintype.card ι - permLength (τ * σ⁻¹)) := by
  rw [gramMatrix_eq_pow_cycleCount]
  congr 1
  have := cycleCount_le (τ * σ⁻¹)
  unfold permLength
  omega

end Weingarten
