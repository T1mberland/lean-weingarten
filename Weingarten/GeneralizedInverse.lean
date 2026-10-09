import Weingarten.Projection

set_option autoImplicit false

/-!
# Spectral generalized inverse and Weingarten coefficients

The scalar inverse in a field sends zero to zero. Applying it to the eigenvalues,
rather than taking the matrix's nonsingular inverse, treats the singular range correctly.
-/

open scoped Matrix ComplexOrder
open Matrix Unitary

namespace Weingarten

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invert the nonzero eigenvalues of a Hermitian matrix and keep its kernel zero. -/
def spectralInverse {A : Matrix n n ℂ} (h : A.IsHermitian) : Matrix n n ℂ :=
  conjStarAlgAut ℂ _ h.eigenvectorUnitary
    (diagonal fun i => ((h.eigenvalues i : ℂ))⁻¹)

/-- The first generalized-inverse equation, including at eigenvalue zero. -/
theorem mul_spectralInverse_mul {A : Matrix n n ℂ} (h : A.IsHermitian) :
    A * spectralInverse h * A = A := by
  let D : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ)⁻¹)
  let C := conjStarAlgAut ℂ _ h.eigenvectorUnitary
  have hA : A = C D := h.spectral_theorem
  have hD : D * E * D = D := by
    simp only [D, E, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : (h.eigenvalues i : ℂ) = 0 <;> simp [hi]
  change A * C E * A = A
  rw [hA, ← map_mul, ← map_mul, hD]

/-- The second generalized-inverse equation. -/
theorem spectralInverse_mul_spectralInverse {A : Matrix n n ℂ} (h : A.IsHermitian) :
    spectralInverse h * A * spectralInverse h = spectralInverse h := by
  let D : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ)⁻¹)
  let C := conjStarAlgAut ℂ _ h.eigenvectorUnitary
  have hA : A = C D := h.spectral_theorem
  have hE : E * D * E = E := by
    simp only [D, E, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : (h.eigenvalues i : ℂ) = 0 <;> simp [hi]
  change C E * A * C E = C E
  rw [hA, ← map_mul, ← map_mul, hE]

theorem spectralInverse_isHermitian {A : Matrix n n ℂ} (h : A.IsHermitian) :
    (spectralInverse h).IsHermitian := by
  change star (spectralInverse h) = spectralInverse h
  unfold spectralInverse
  rw [← map_star]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.star_apply]
  · simp [Matrix.star_apply, Matrix.diagonal, hij, Ne.symm hij]

theorem commute_spectralInverse {A : Matrix n n ℂ} (h : A.IsHermitian) :
    Commute A (spectralInverse h) := by
  let D : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ)⁻¹)
  let C := conjStarAlgAut ℂ _ h.eigenvectorUnitary
  have hA : A = C D := h.spectral_theorem
  change A * C E = C E * A
  rw [hA, ← map_mul, ← map_mul]
  congr 1
  exact Matrix.commute_diagonal _ _

/-- The remaining Moore–Penrose equations: the two products are Hermitian. -/
theorem mul_spectralInverse_isHermitian {A : Matrix n n ℂ} (h : A.IsHermitian) :
    (A * spectralInverse h).IsHermitian := by
  change (A * spectralInverse h)ᴴ = A * spectralInverse h
  rw [Matrix.conjTranspose_mul, (spectralInverse_isHermitian h).eq, h.eq]
  exact (commute_spectralInverse h).eq.symm

theorem spectralInverse_mul_isHermitian {A : Matrix n n ℂ} (h : A.IsHermitian) :
    (spectralInverse h * A).IsHermitian := by
  rw [← (commute_spectralInverse h).eq]
  exact mul_spectralInverse_isHermitian h

/-- The canonical spectral inverse of the permutation Gram matrix. -/
def weingartenMatrix (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℂ :=
  spectralInverse (gramMatrix_posSemidef (ι := ι) (α := α)).isHermitian

theorem gram_weingarten_gram (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    gramMatrix (ι := ι) (α := α) * weingartenMatrix ι α * gramMatrix (ι := ι) (α := α) =
      gramMatrix (ι := ι) (α := α) :=
  mul_spectralInverse_mul _

/-- The spectral construction agrees with the ordinary matrix inverse in the stable range. -/
theorem weingartenMatrix_eq_inv {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (e : ι ↪ α) :
    weingartenMatrix ι α = (gramMatrix (ι := ι) (α := α))⁻¹ := by
  let G := gramMatrix (ι := ι) (α := α)
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp (gramMatrix_posDef e).isUnit
  have h := congr_arg (fun X => G⁻¹ * X * G⁻¹) (gram_weingarten_gram ι α)
  change G⁻¹ * (G * weingartenMatrix ι α * G) * G⁻¹ = G⁻¹ * G * G⁻¹ at h
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul] at h
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one] using h

end

end Weingarten
