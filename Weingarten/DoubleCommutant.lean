import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The finite-group double-commutant theorem

The intended application is the permutation action on tensor powers. Maschke's
theorem and Jacobson density apply even when that action is not faithful, which
is essential for moment orders larger than the matrix dimension.
-/

set_option autoImplicit false

open scoped BigOperators
open Module

namespace Weingarten

noncomputable section

/-- Finite-dimensional form of Jacobson density, expressed using ordinary
linear maps and an explicit commutation hypothesis. -/
theorem exists_smul_of_commutes
    {K R V : Type*} [Field K] [Ring R] [AddCommGroup V]
    [Module K V] [Module R V] [SMulCommClass R K V]
    [FiniteDimensional K V] [IsSemisimpleModule R V]
    (T : Module.End K V)
    (hT : ∀ f : Module.End R V, ∀ v, T (f v) = f (T v)) :
    ∃ r : R, ∀ v, T v = r • v := by
  classical
  let F : Module.End (Module.End R V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f v => hT f v }
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨r, ?_⟩
  have heq : T = Module.toModuleEnd K (S := R) V r := by
    apply b.ext
    intro i
    exact hr (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  intro v
  exact congr_arg (fun f : Module.End K V => f v) heq

/-- The bicommutant of a complex finite-group representation is its linear span.
No faithfulness or dimension bound is assumed. -/
theorem exists_sum_representation_of_commutes
    {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ f : Module.End ℂ V, (∀ g, Commute f (ρ g)) → Commute T f) :
    ∃ c : G → ℂ, T = ∑ g, c g • ρ g := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by simp [Nat.card_eq_fintype_card]⟩
  let e := ρ.asModuleEquiv
  let T' : Module.End ℂ ρ.asModule := e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap
  have hT' : ∀ f : Module.End (MonoidAlgebra ℂ G) ρ.asModule, ∀ v, T' (f v) = f (T' v) := by
    intro f v
    let f' : Module.End ℂ V := e.toLinearMap ∘ₗ f.restrictScalars ℂ ∘ₗ e.symm.toLinearMap
    have hf' : ∀ g, Commute f' (ρ g) := by
      intro g
      apply LinearMap.ext
      intro w
      change e (f (e.symm (ρ g w))) = ρ g (e (f (e.symm w)))
      rw [ρ.asModuleEquiv_symm_map_rho, f.map_smul, ρ.asModuleEquiv_map_smul,
        ρ.asAlgebraHom_of]
    have h := congr_arg (fun A : Module.End ℂ V => A (e v)) (hT f' hf').eq
    apply e.injective
    simpa [T', f'] using h
  obtain ⟨a, ha⟩ := exists_smul_of_commutes T' hT'
  have hTa : T = ρ.asAlgebraHom a := by
    apply LinearMap.ext
    intro v
    have h := congr_arg e (ha (e.symm v))
    simpa [T', Representation.asModuleEquiv_map_smul] using h
  refine ⟨fun g => a g, ?_⟩
  rw [hTa]
  have hsum : a = ∑ g : G, MonoidAlgebra.single g (a g) :=
    (Finsupp.univ_sum_single a).symm
  conv_lhs => rw [hsum, map_sum]
  simp only [Representation.asAlgebraHom_single]

end

end Weingarten
