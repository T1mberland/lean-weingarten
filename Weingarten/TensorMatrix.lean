import Weingarten.HaarProjection
import Weingarten.DoubleCommutant

/-! # Tensor matrices and the permutation representation -/

set_option autoImplicit false

open scoped Matrix BigOperators
open Matrix

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

/-- The matrix of an arbitrary tensor power, also for nonunitary matrices. -/
def tensorMatrix {R : Type*} [CommSemiring R] (p : ℕ) (M : Matrix α α R) :
    Matrix (Fin p → α) (Fin p → α) R := fun i j => ∏ a, M (i a) (j a)

omit [DecidableEq α] in
theorem tensorMatrix_mul {R : Type*} [CommSemiring R] (M N : Matrix α α R) :
    tensorMatrix p (M * N) = tensorMatrix p M * tensorMatrix p N := by
  ext i j
  simp only [tensorMatrix, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

omit [Fintype α] in
@[simp] theorem tensorMatrix_one {R : Type*} [CommSemiring R] :
    tensorMatrix p (1 : Matrix α α R) = 1 := by
  ext i j
  simp only [tensorMatrix, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp
  · rw [if_neg h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

/-- Permutation matrices on words. Their vectorizations are the existing diagrams. -/
def permutationTensor (σ : Equiv.Perm (Fin p)) : Matrix (Fin p → α) (Fin p → α) ℂ :=
  fun i j => pairing σ i j

@[simp] theorem permutationTensor_mulVec (σ : Equiv.Perm (Fin p)) (v : (Fin p → α) → ℂ)
    (i : Fin p → α) : (permutationTensor σ *ᵥ v) i = v (i ∘ σ) := by
  simp [permutationTensor, pairing, Matrix.mulVec, dotProduct]

/-- Permuting tensor positions is a representation even in the nonfaithful range. -/
def permutationRepresentation (α : Type*) [Fintype α] [DecidableEq α] (p : ℕ) :
    Representation ℂ (Equiv.Perm (Fin p)) ((Fin p → α) → ℂ) where
  toFun σ :=
    { toFun := fun v i => v (i ∘ σ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toLin_permutationTensor (σ : Equiv.Perm (Fin p)) :
    Matrix.toLinAlgEquiv' (permutationTensor (α := α) σ) =
      permutationRepresentation α p σ := by
  apply LinearMap.ext
  intro v
  funext i
  exact permutationTensor_mulVec σ v i

/-- The finite-group double commutant, specialized to tensor-position permutations. -/
theorem permutationTensor_bicommutant
    (X : Matrix (Fin p → α) (Fin p → α) ℂ)
    (hX : ∀ Y : Matrix (Fin p → α) (Fin p → α) ℂ,
      (∀ σ, Commute Y (permutationTensor σ)) → Commute X Y) :
    ∃ c : Equiv.Perm (Fin p) → ℂ, X = ∑ σ, c σ • permutationTensor σ := by
  let e := Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin p → α)
  have h : ∀ f, (∀ σ, Commute f (permutationRepresentation α p σ)) → Commute (e X) f := by
    intro f hf
    have hY : ∀ σ, Commute (e.symm f) (permutationTensor σ) := by
      intro σ
      apply e.injective
      simpa only [e, map_mul, AlgEquiv.apply_symm_apply, toLin_permutationTensor] using (hf σ).eq
    have := (hX (e.symm f) hY).map e.toMonoidHom
    simpa using this
  obtain ⟨c, hc⟩ := exists_sum_representation_of_commutes (permutationRepresentation α p) (e X) h
  refine ⟨c, e.injective ?_⟩
  simpa only [e, map_sum, map_smul, toLin_permutationTensor] using hc

theorem permutationTensor_mul_apply (σ : Equiv.Perm (Fin p))
    (Y : Matrix (Fin p → α) (Fin p → α) ℂ) (i j : Fin p → α) :
    (permutationTensor (α := α) σ * Y) i j = Y (i ∘ σ) j := by
  simp [Matrix.mul_apply, permutationTensor, pairing]

theorem mul_permutationTensor_apply (σ : Equiv.Perm (Fin p))
    (Y : Matrix (Fin p → α) (Fin p → α) ℂ) (i j : Fin p → α) :
    (Y * permutationTensor (α := α) σ) i j = Y i (j ∘ σ.symm) := by
  have h (a : Fin p → α) : j = a ∘ σ ↔ a = j ∘ σ.symm := by
    constructor
    · intro h
      funext b
      simpa using (congr_fun h (σ.symm b)).symm
    · rintro rfl
      ext b
      simp
  simp [Matrix.mul_apply, permutationTensor, pairing, h]

/-- Commuting with tensor-position permutations means that entries are constant
under simultaneous permutations of their row and column words. -/
theorem simultaneous_reindex_of_commute
    (Y : Matrix (Fin p → α) (Fin p → α) ℂ)
    (hY : ∀ σ, Commute Y (permutationTensor σ))
    (σ : Equiv.Perm (Fin p)) (i j : Fin p → α) :
    Y (i ∘ σ) (j ∘ σ) = Y i j := by
  have h := congr_fun (congr_fun (hY σ).eq i) (j ∘ σ)
  simp only [mul_permutationTensor_apply, permutationTensor_mul_apply] at h
  have hj : (j ∘ σ) ∘ σ.symm = j := by ext a; simp
  rw [hj] at h
  exact h.symm

end

end Weingarten
