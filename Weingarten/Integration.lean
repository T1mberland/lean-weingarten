import Weingarten.TensorPower
import Weingarten.GeneralizedInverse

set_option autoImplicit false

/-!
# Conditional reduction of the general integration formula

This file states exactly the missing bridge to invariant theory as an explicit
spanning hypothesis, not as an axiom or hidden typeclass assumption. It is not an
unconditional proof of the general Weingarten formula.
-/

open scoped Matrix BigOperators

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

/-- Only the spanning assertion remains to obtain the arbitrary-order matrix formula. -/
theorem momentMatrix_eq_of_span
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B) :
    momentMatrix α p = diagramMatrix * weingartenMatrix (Fin p) α * diagramMatrixᴴ :=
  momentMatrix_eq_of_projection_hypotheses momentMatrix_conjTranspose
    momentMatrix_mul_diagramMatrix hspan

/-- General Weingarten integration, **conditional on the unproved spanning assertion**.
There is no restriction on dimension or moment order in this reduction theorem. -/
theorem mixedMoment_eq_of_span
    (hspan : ∃ B, momentMatrix α p = diagramMatrix * B)
    (i j i' j' : Fin p → α) :
    mixedMoment i j i' j' =
      ∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin p),
        pairing σ i i' * weingartenMatrix (Fin p) α σ τ * pairing τ j j' :=
  mixedMoment_eq_of_projection_hypotheses momentMatrix_conjTranspose
    momentMatrix_mul_diagramMatrix hspan i j i' j'

end Weingarten
