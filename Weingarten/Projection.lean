import Weingarten.Permutation

/-!
# Reconstruction from a possibly singular Gram matrix

This is finite-dimensional linear algebra, not yet the Haar integration theorem.
The hypotheses that a Haar moment matrix is Hermitian, fixes permutation tensors,
and has its columns in their span must be supplied separately.
-/

open scoped Matrix ComplexOrder

namespace Weingarten

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A vector-valued matrix in the range of `A` and orthogonal to that range vanishes. -/
theorem mul_eq_zero_of_gram_mul_eq_zero (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (h : Aᴴ * (A * B) = 0) : A * B = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, h, Matrix.mul_zero, Matrix.trace_zero]

/-- A Hermitian projection onto the column span of `A` is reconstructed by any
generalized inverse `W` of its Gram matrix. Only `G W G = G` is required, so the
statement remains valid when the Gram matrix is singular. -/
theorem projection_eq_of_generalizedInverse
    (A : Matrix m n ℂ) (P : Matrix m m ℂ) (W : Matrix n n ℂ)
    (hHerm : Pᴴ = P) (hfix : P * A = A)
    (hspan : ∃ B : Matrix n m ℂ, P = A * B)
    (hW : (Aᴴ * A) * W * (Aᴴ * A) = Aᴴ * A) :
    P = A * W * Aᴴ := by
  obtain ⟨B, hB⟩ := hspan
  have hleft : Aᴴ * P = Aᴴ := by
    have h := congr_arg Matrix.conjTranspose hfix
    simpa only [Matrix.conjTranspose_mul, hHerm] using h
  have hGB : (Aᴴ * A) * B = Aᴴ := by
    rw [Matrix.mul_assoc, ← hB, hleft]
  have hzero : Aᴴ * (A * (B - W * Aᴴ)) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, hGB]
    conv_rhs => rw [← sub_self Aᴴ]
    congr 1
    calc
      (Aᴴ * A) * (W * Aᴴ) = ((Aᴴ * A) * W * (Aᴴ * A)) * B := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hGB]
        simp only [Matrix.mul_assoc]
      _ = Aᴴ := by rw [hW, hGB]
  have h := mul_eq_zero_of_gram_mul_eq_zero A (B - W * Aᴴ) hzero
  rw [Matrix.mul_sub, ← hB, ← Matrix.mul_assoc, sub_eq_zero] at h
  exact h

/-- In the stable range the Gram matrix has an ordinary inverse. -/
theorem gramMatrix_inv_mul {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] (e : ι ↪ α) :
    (gramMatrix (ι := ι) (α := α))⁻¹ * gramMatrix (ι := ι) (α := α) = 1 := by
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gramMatrix_posDef e).isUnit)

end Weingarten
