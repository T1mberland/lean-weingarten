import Weingarten.InvariantSpanning
import Weingarten.GeneralizedInverse

set_option autoImplicit false

/-!
# The general unitary Weingarten integration formula

The spanning theorem is proved in `InvariantSpanning`. The main results at the
end of this file have no projection, invariant-theory, or stable-range hypotheses.
The earlier conditional lemmas remain available as reusable reconstruction APIs.
-/

open scoped Matrix BigOperators
open MeasureTheory

namespace Weingarten

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

/-- The general matrix formula follows if the Haar moment matrix is the Hermitian
projection onto the permutation tensors. All three obligations are explicit. -/
theorem momentMatrix_eq_of_projection_hypotheses
    (hHerm : (momentMatrix α p)ᴴ = momentMatrix α p)
    (hfix : momentMatrix α p * diagramMatrix = diagramMatrix)
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B) :
    momentMatrix α p = diagramMatrix * weingartenMatrix (Fin p) α * diagramMatrixᴴ :=
  projection_eq_of_generalizedInverse _ _ _ hHerm hfix hspan
    (gram_weingarten_gram (Fin p) α)

/-- The coordinate version of the conditional formula, valid without a stable-range
restriction once the three displayed projection hypotheses have been established. -/
theorem mixedMoment_eq_of_projection_hypotheses
    (hHerm : (momentMatrix α p)ᴴ = momentMatrix α p)
    (hfix : momentMatrix α p * diagramMatrix = diagramMatrix)
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B)
    (i j i' j' : Fin p → α) :
    mixedMoment i j i' j' =
      ∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin p),
        pairing σ i i' * weingartenMatrix (Fin p) α σ τ * pairing τ j j' := by
  have h := congr_fun (congr_fun
    (momentMatrix_eq_of_projection_hypotheses hHerm hfix hspan) (i, i')) (j, j')
  simp only [momentMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, diagramMatrix,
    star_pairing, Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  exact h

/-- A reconstruction API for any supplied spanning factorization. -/
theorem momentMatrix_eq_of_span
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B) :
    momentMatrix α p = diagramMatrix * weingartenMatrix (Fin p) α * diagramMatrixᴴ :=
  momentMatrix_eq_of_projection_hypotheses momentMatrix_conjTranspose
    momentMatrix_mul_diagramMatrix hspan

/-- A coordinate reconstruction API for any supplied spanning factorization. -/
theorem mixedMoment_eq_of_span
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B)
    (i j i' j' : Fin p → α) :
    mixedMoment i j i' j' =
      ∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin p),
        pairing σ i i' * weingartenMatrix (Fin p) α σ τ * pairing τ j j' :=
  mixedMoment_eq_of_projection_hypotheses momentMatrix_conjTranspose
    momentMatrix_mul_diagramMatrix hspan i j i' j'

/-- The general Haar moment matrix is reconstructed from the spectral Weingarten
matrix, including the singular Gram matrix regime. -/
theorem momentMatrix_eq_weingarten :
    momentMatrix α p = diagramMatrix * weingartenMatrix (Fin p) α * diagramMatrixᴴ :=
  momentMatrix_eq_of_span momentMatrix_factorization

/-- **The general unitary Weingarten formula**, with no relation required between
the matrix dimension and moment order. -/
theorem mixedMoment_eq_weingarten (i j i' j' : Fin p → α) :
    mixedMoment i j i' j' =
      ∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin p),
        pairing σ i i' * weingartenMatrix (Fin p) α σ τ * pairing τ j j' :=
  mixedMoment_eq_of_span momentMatrix_factorization i j i' j'

/-- **The general unitary Weingarten integration formula** as an explicit Haar
integral. The Weingarten matrix is the Moore–Penrose inverse of the permutation
Gram matrix, so this statement applies in particular when `card α < p`. -/
theorem integral_unitary_weingarten (i j i' j' : Fin p → α) :
    (∫ U : UnitaryGroup α,
      (∏ a, U (i a) (j a)) * star (∏ a, U (i' a) (j' a)) ∂haar α) =
      ∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin p),
        pairing σ i i' * weingartenMatrix (Fin p) α σ τ * pairing τ j j' :=
  mixedMoment_eq_weingarten i j i' j'

end Weingarten
