import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false

/-!
# Permutation tensors and their Gram matrix

Positions and matrix indices are arbitrary finite types. Our convention is
`pairing σ i j = 1` exactly when `j = i ∘ σ`.
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace Weingarten

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The Kronecker delta attached to a permutation of tensor positions. -/
def pairing (σ : Equiv.Perm ι) (i j : ι → α) : ℂ :=
  if j = i ∘ σ then 1 else 0

/-- Columns are permutation tensors, in the coordinate basis indexed by pairs of words. -/
def diagramMatrix : Matrix ((ι → α) × (ι → α)) (Equiv.Perm ι) ℂ :=
  fun p σ => pairing σ p.1 p.2

/-- The Gram matrix of the permutation tensors. This definition also covers the singular range. -/
def gramMatrix : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℂ :=
  (diagramMatrix (ι := ι) (α := α))ᴴ * diagramMatrix

omit [DecidableEq ι] [Fintype α] in
@[simp] theorem star_pairing (σ : Equiv.Perm ι) (i j : ι → α) :
    star (pairing σ i j) = pairing σ i j := by
  simp [pairing]

/-- A Gram entry counts words whose two reindexings agree. -/
theorem gramMatrix_apply (σ τ : Equiv.Perm ι) :
    gramMatrix (α := α) σ τ =
      ∑ i : ι → α, if i ∘ σ = i ∘ τ then (1 : ℂ) else 0 := by
  classical
  simp only [gramMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, diagramMatrix,
    star_pairing, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [pairing, eq_comm]

/-- Every permutation tensor has squared norm `card α ^ card ι`. -/
@[simp] theorem gramMatrix_diag (σ : Equiv.Perm ι) :
    gramMatrix (α := α) σ σ = (Fintype.card α : ℂ) ^ Fintype.card ι := by
  simp [gramMatrix_apply]

theorem gramMatrix_posSemidef : (gramMatrix (ι := ι) (α := α)).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype α] in
/-- An injective word separates all permutation tensors. -/
theorem pairing_injective (e : ι ↪ α) (σ τ : Equiv.Perm ι) :
    pairing σ e (e ∘ τ) = if σ = τ then 1 else 0 := by
  have h : e ∘ τ = e ∘ σ ↔ σ = τ := by
    constructor
    · intro h
      apply Equiv.ext
      intro a
      exact (e.injective (congr_fun h a)).symm
    · rintro rfl
      rfl
  simp only [pairing, h]

omit [Fintype α] in
/-- In the stable range, reading one row recovers each coefficient of a tensor sum. -/
theorem diagramMatrix_mulVec_embedding (e : ι ↪ α) (c : Equiv.Perm ι → ℂ)
    (τ : Equiv.Perm ι) :
    (diagramMatrix *ᵥ c) (e, e ∘ τ) = c τ := by
  simp [Matrix.mulVec, dotProduct, diagramMatrix, pairing_injective]

omit [Fintype α] in
/-- Permutation tensors are independent whenever the positions embed into the indices. -/
theorem diagramMatrix_mulVec_injective (e : ι ↪ α) :
    Function.Injective (diagramMatrix (ι := ι) (α := α)).mulVec := by
  intro c d h
  funext τ
  have := congr_fun h (e, e ∘ τ)
  simpa only [diagramMatrix_mulVec_embedding] using this

theorem gramMatrix_posDef (e : ι ↪ α) :
    (gramMatrix (ι := ι) (α := α)).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (diagramMatrix_mulVec_injective e)

end Weingarten
