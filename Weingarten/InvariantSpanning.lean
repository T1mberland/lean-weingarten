import Weingarten.SchurWeyl

/-! # Permutation tensors span all unitary invariant tensors -/

set_option autoImplicit false

open scoped Matrix BigOperators
open Matrix

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

theorem tensorMatrix_unitary_conjTranspose (U : UnitaryGroup α) :
    (tensorMatrix p U.val)ᴴ = tensorMatrix p U⁻¹.val := by
  ext i j
  exact (entryProduct_inv U i j).symm

theorem tensorMatrix_unitary_conjTranspose_mul (U : UnitaryGroup α) :
    (tensorMatrix p U.val)ᴴ * tensorMatrix p U.val = 1 := by
  rw [tensorMatrix_unitary_conjTranspose, ← tensorMatrix_mul]
  have h : U⁻¹.val * U.val = 1 := U.2.1
  rw [h, tensorMatrix_one]

/-- Vectorization identifies the mixed tensor action with conjugation. -/
theorem mixedAction_mulVec_eq_conjugation (U : UnitaryGroup α)
    (X : Matrix (Fin p → α) (Fin p → α) ℂ) :
    mixedAction p U *ᵥ (fun r => X r.1 r.2) =
      fun r => (tensorMatrix p U.val * X * (tensorMatrix p U.val)ᴴ) r.1 r.2 := by
  funext ⟨i, i'⟩
  simp only [Matrix.mulVec, dotProduct, mixedAction, mixedMonomial, entryProduct,
    tensorMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- **The permutation-tensor spanning theorem**, without any dimension bound. -/
theorem invariantTensors_le_range_diagramMatrix :
    invariantTensors α p ≤ LinearMap.range (diagramMatrix (ι := Fin p) (α := α)).mulVecLin := by
  intro v hv
  let X : Matrix (Fin p → α) (Fin p → α) ℂ := fun i j => v (i, j)
  have hX : ∀ U : UnitaryGroup α, Commute X (tensorMatrix p U.val) := by
    intro U
    have hinv : tensorMatrix p U.val * X * (tensorMatrix p U.val)ᴴ = X := by
      ext i j
      have h := congr_fun ((mem_invariantTensors_iff v).mp hv U) (i, j)
      change (mixedAction p U *ᵥ (fun r => X r.1 r.2)) (i, j) = X i j at h
      rw [mixedAction_mulVec_eq_conjugation] at h
      exact h
    have h := congr_arg (fun A => A * tensorMatrix p U.val) hinv
    simp only [Matrix.mul_assoc, tensorMatrix_unitary_conjTranspose_mul, Matrix.mul_one] at h
    exact h.symm
  obtain ⟨c, hc⟩ := unitary_tensor_commutant X hX
  refine ⟨c, ?_⟩
  funext ⟨i, j⟩
  have h := congr_fun (congr_fun hc i) j
  change (∑ σ, pairing σ i j * c σ) = v (i, j)
  simpa [X, permutationTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
    using h.symm

/-- The previously missing factorization of the actual Haar moment matrix. -/
theorem momentMatrix_factorization :
    ∃ B, momentMatrix α p = diagramMatrix * B :=
  momentMatrix_factorization_iff_invariantTensors_le.mpr
    invariantTensors_le_range_diagramMatrix

end

end Weingarten
