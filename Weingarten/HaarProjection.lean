import Weingarten.TensorPower

/-!
# Haar averaging projects onto the invariant tensors

This is the analytic part of the remaining spanning problem. It identifies the
range of the actual moment matrix with the fixed vectors of the mixed tensor
representation, without an invariant-theory assumption.
-/

set_option autoImplicit false

open scoped BigOperators Matrix
open MeasureTheory

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

/-- Coordinates for the mixed tensor representation of balanced degree `p`. -/
abbrev TensorIndex (α : Type*) (p : ℕ) := (Fin p → α) × (Fin p → α)

/-- The action of `U` on the mixed tensor power. -/
def mixedAction (p : ℕ) (U : UnitaryGroup α) :
    Matrix (TensorIndex α p) (TensorIndex α p) ℂ :=
  fun r c => mixedMonomial r.1 c.1 r.2 c.2 U

theorem entryProduct_mul (U V : UnitaryGroup α) (i j : Fin p → α) :
    entryProduct i j (U * V) =
      ∑ a : Fin p → α, entryProduct i a U * entryProduct a j V := by
  simp only [entryProduct, Matrix.UnitaryGroup.mul_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.prod_mul_distrib

theorem mixedAction_mul (U V : UnitaryGroup α) :
    mixedAction p (U * V) = mixedAction p U * mixedAction p V := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [mixedAction, mixedMonomial, entryProduct_mul, star_sum, star_mul,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Haar averaging is fixed by left multiplication by the representation. -/
theorem mixedAction_mul_momentMatrix (U : UnitaryGroup α) :
    mixedAction p U * momentMatrix α p = momentMatrix α p := by
  ext r c
  simp only [Matrix.mul_apply, momentMatrix, mixedMoment]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum _ (fun a _ =>
    (integrable_mixedMonomial a.1 c.1 a.2 c.2).const_mul _)]
  change (∫ V, (mixedAction p U * mixedAction p V) r c ∂haar α) = _
  simp_rw [← mixedAction_mul]
  exact integral_mul_left_eq_self _ _

/-- The invariant tensors as a concrete subspace of coordinate vectors. -/
def invariantTensors (α : Type*) [Fintype α] [DecidableEq α] (p : ℕ) :
    Submodule ℂ (TensorIndex α p → ℂ) where
  carrier := {v | ∀ U : UnitaryGroup α, mixedAction p U *ᵥ v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw U
    simp only [Matrix.mulVec_add, hv U, hw U]
  smul_mem' := by
    intro c v hv U
    simp only [Matrix.mulVec_smul, hv U]

theorem mem_invariantTensors_iff (v : TensorIndex α p → ℂ) :
    v ∈ invariantTensors α p ↔ ∀ U : UnitaryGroup α, mixedAction p U *ᵥ v = v := Iff.rfl

/-- Every Haar-averaged vector is invariant. -/
theorem momentMatrix_mulVec_mem_invariantTensors (v : TensorIndex α p → ℂ) :
    momentMatrix α p *ᵥ v ∈ invariantTensors α p := by
  intro U
  rw [Matrix.mulVec_mulVec, mixedAction_mul_momentMatrix]

/-- Haar averaging acts as the identity on every invariant tensor. -/
theorem momentMatrix_mulVec_of_invariant {v : TensorIndex α p → ℂ}
    (hv : v ∈ invariantTensors α p) : momentMatrix α p *ᵥ v = v := by
  funext r
  simp only [Matrix.mulVec, dotProduct, momentMatrix, mixedMoment]
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun a _ =>
    (integrable_mixedMonomial r.1 a.1 r.2 a.2).mul_const _)]
  change (∫ U, (mixedAction p U *ᵥ v) r ∂haar α) = v r
  have hv' := (mem_invariantTensors_iff v).mp hv
  simp only [hv', integral_const, probReal_univ, one_smul]

/-- Exact range identification; neither inclusion uses a spanning assumption. -/
theorem range_momentMatrix :
    LinearMap.range (momentMatrix α p).mulVecLin = invariantTensors α p := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact momentMatrix_mulVec_mem_invariantTensors w
  · intro v hv
    exact ⟨v, momentMatrix_mulVec_of_invariant hv⟩

/-- The moment matrix is idempotent, as expected for normalized Haar averaging. -/
theorem momentMatrix_idempotent : momentMatrix α p * momentMatrix α p = momentMatrix α p := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec]
  exact momentMatrix_mulVec_of_invariant (momentMatrix_mulVec_mem_invariantTensors v)

/-- Each column of the permutation diagram matrix is invariant. -/
theorem diagramMatrix_col_mem_invariantTensors (σ : Equiv.Perm (Fin p)) :
    (diagramMatrix (α := α)).col σ ∈ invariantTensors α p := by
  have h : momentMatrix α p *ᵥ (diagramMatrix (α := α)).col σ =
      (diagramMatrix (α := α)).col σ := by
    funext r
    exact congr_fun (congr_fun momentMatrix_mul_diagramMatrix r) σ
  rw [← h]
  exact momentMatrix_mulVec_mem_invariantTensors _

/-- Spanning the invariant tensors is equivalent to the original matrix factorization.
This equivalence makes the remaining algebraic theorem precise. -/
theorem momentMatrix_factorization_iff_invariantTensors_le :
    (∃ B, momentMatrix α p = diagramMatrix * B) ↔
      invariantTensors α p ≤ LinearMap.range (diagramMatrix (ι := Fin p) (α := α)).mulVecLin := by
  constructor
  · rintro ⟨B, hB⟩ v hv
    refine ⟨B *ᵥ v, ?_⟩
    change diagramMatrix *ᵥ (B *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← hB, momentMatrix_mulVec_of_invariant hv]
  · intro h
    have hc : ∀ c : TensorIndex α p, ∃ b, diagramMatrix *ᵥ b = (momentMatrix α p).col c := by
      intro c
      apply h
      rw [← range_momentMatrix]
      exact ⟨Pi.single c 1, by simp⟩
    choose b hb using hc
    refine ⟨fun σ c => b c σ, ?_⟩
    ext r c
    exact (congr_fun (hb c) r).symm

end

end Weingarten
