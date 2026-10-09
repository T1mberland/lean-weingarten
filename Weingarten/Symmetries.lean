import Weingarten.Haar
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false

/-! # Explicit unitary matrices implementing row and column symmetries -/

namespace Weingarten

open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation matrix as a unitary matrix. -/
def permutationUnitary (σ : Equiv.Perm α) : UnitaryGroup α :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

@[simp] theorem permutationUnitary_mul_apply (σ : Equiv.Perm α) (U : UnitaryGroup α)
    (i j : α) : (permutationUnitary σ * U) i j = U (σ i) j := by
  change (σ.permMatrix ℂ * U.val) i j = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

/-- A diagonal sign change in one coordinate. -/
def signUnitary (a : α) : UnitaryGroup α :=
  ⟨Matrix.diagonal (fun i => if i = a then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = a <;> simp [hi]
    · simp [hij]⟩

@[simp] theorem signUnitary_mul_apply (a : α) (U : UnitaryGroup α) (i j : α) :
    (signUnitary a * U) i j = (if i = a then (-1 : ℂ) else 1) * U i j := by
  exact Matrix.diagonal_mul _ _ _ _

@[simp] theorem mul_signUnitary_apply (a : α) (U : UnitaryGroup α) (i j : α) :
    (U * signUnitary a) i j = U i j * (if j = a then (-1 : ℂ) else 1) := by
  exact Matrix.mul_diagonal _ _ _ _

end Weingarten
