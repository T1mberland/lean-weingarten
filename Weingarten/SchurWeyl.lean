import Weingarten.TensorMatrix
import Weingarten.PolynomialSpan
import Weingarten.WordWeight
import Weingarten.UnitaryPolynomial

/-!
# The unitary Schur–Weyl commutant theorem in all dimensions

Polynomial uniqueness extends commutation from unitary to arbitrary matrices.
Monomial multiplicities describe the commutant of the permutation action, and
the finite-group double-commutant theorem finishes the argument. No stable-range
assumption is used.
-/

set_option autoImplicit false

open scoped Matrix BigOperators
open Matrix MvPolynomial

namespace Weingarten

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}

/-- The commutant of the position permutations is spanned by tensor powers of
arbitrary matrices, including when different words have the same multiplicities. -/
theorem permutation_commutant_mem_tensorMatrix_span
    (Y : Matrix (Fin p → α) (Fin p → α) ℂ)
    (hY : ∀ σ, Commute Y (permutationTensor σ)) :
    Y ∈ Submodule.span ℂ (Set.range (tensorMatrix (α := α) (R := ℂ) p)) := by
  classical
  let w : TensorIndex α p → (α × α) →₀ ℕ :=
    fun r => wordWeight (fun a => (r.1 a, r.2 a))
  have hv : ∀ r s : TensorIndex α p, w r = w s → Y r.1 r.2 = Y s.1 s.2 := by
    intro r s hrs
    obtain ⟨σ, hσ⟩ := exists_perm_of_wordWeight_eq
      (fun a => (r.1 a, r.2 a)) (fun a => (s.1 a, s.2 a)) hrs
    have hs1 : s.1 = r.1 ∘ σ := congr_arg (fun f a => (f a).1) hσ
    have hs2 : s.2 = r.2 ∘ σ := congr_arg (fun f a => (f a).2) hσ
    rw [hs1, hs2]
    exact (simultaneous_reindex_of_commute Y hY σ r.1 r.2).symm
  have hspan := mem_span_monomial_evaluations w (fun r => Y r.1 r.2) hv
  let S := Submodule.span ℂ (Set.range (tensorMatrix (α := α) (R := ℂ) p))
  have hc : ∀ v ∈ Submodule.span ℂ (Set.range (fun z : α × α → ℂ =>
      fun r : TensorIndex α p => eval z (monomial (w r) (1 : ℂ)))),
      (fun i j => v (i, j)) ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨fun i j => z (i, j), ?_⟩
      ext i j
      exact (eval_monomial_wordWeight (fun a => (i a, j a)) z).symm
    | zero => exact S.zero_mem
    | add x y hx hy ihx ihy => exact S.add_mem ihx ihy
    | smul c v hv ih => exact S.smul_mem c ih
  exact hc _ hspan

/-- Polynomial uniqueness extends a unitary commutation identity to all matrices. -/
theorem commute_tensorMatrix_of_unitary
    (X : Matrix (Fin p → α) (Fin p → α) ℂ)
    (hX : ∀ U : UnitaryGroup α, Commute X (tensorMatrix p U.val))
    (M : Matrix α α ℂ) : Commute X (tensorMatrix p M) := by
  ext i j
  let Z : Matrix α α (MvPolynomial (α × α) ℂ) := fun a b => MvPolynomial.X (a, b)
  let XC : Matrix (Fin p → α) (Fin p → α) (MvPolynomial (α × α) ℂ) := X.map C
  let q : MvPolynomial (α × α) ℂ :=
    (XC * tensorMatrix p Z - tensorMatrix p Z * XC) i j
  have hq (N : Matrix α α ℂ) :
      eval (fun ab => N ab.1 ab.2) q =
        (X * tensorMatrix p N - tensorMatrix p N * X) i j := by
    simp [q, Z, XC, Matrix.sub_apply, Matrix.mul_apply, tensorMatrix,
      Matrix.map_apply, map_sum, map_prod]
  have hunit : ∀ U : UnitaryGroup α, eval (fun ab => U ab.1 ab.2) q = 0 := by
    intro U
    rw [hq, Matrix.sub_apply]
    exact sub_eq_zero.mpr (congr_fun (congr_fun (hX U).eq i) j)
  have h := polynomial_eq_zero_of_unitary q hunit M
  rw [hq, Matrix.sub_apply] at h
  exact sub_eq_zero.mp h

/-- **Unitary Schur–Weyl duality**, in matrix coordinates. Any endomorphism
commuting with all unitary tensor powers is a linear combination of position
permutations. This includes nonfaithful permutation representations. -/
theorem unitary_tensor_commutant
    (X : Matrix (Fin p → α) (Fin p → α) ℂ)
    (hX : ∀ U : UnitaryGroup α, Commute X (tensorMatrix p U.val)) :
    ∃ c : Equiv.Perm (Fin p) → ℂ, X = ∑ σ, c σ • permutationTensor σ := by
  apply permutationTensor_bicommutant X
  intro Y hY
  have hmem := permutation_commutant_mem_tensorMatrix_span Y hY
  clear hY
  induction hmem using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨M, rfl⟩ := hY
    exact commute_tensorMatrix_of_unitary X hX M
  | zero => exact Commute.zero_right X
  | add A B hA hB ihA ihB => exact ihA.add_right ihB
  | smul c A hA ih =>
    change X * (c • A) = (c • A) * X
    simp only [mul_smul_comm, smul_mul_assoc, ih.eq]

end

end Weingarten
