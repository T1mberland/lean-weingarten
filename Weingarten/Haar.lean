import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! # Normalized Haar measure on finite-dimensional unitary groups -/

open scoped BigOperators
open Matrix MeasureTheory

namespace Weingarten

/-- The unitary group of complex matrices with indices in `α`. -/
abbrev UnitaryGroup (α : Type*) [Fintype α] [DecidableEq α] := Matrix.unitaryGroup α ℂ

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Row orthonormality, in the convention used by mixed moments. -/
theorem sum_row_mul_conj (U : UnitaryGroup α) (i j : α) :
    ∑ k, U i k * star (U j k) = if i = j then 1 else 0 := by
  have h := congr_fun (congr_fun U.2.2 i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

/-- Column orthonormality. -/
theorem sum_conj_mul_column (U : UnitaryGroup α) (i j : α) :
    ∑ k, star (U k i) * U k j = if i = j then 1 else 0 := by
  have h := congr_fun (congr_fun U.2.1 i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

theorem sum_normSq_row (U : UnitaryGroup α) (i : α) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congr_arg Complex.re (sum_row_mul_conj U i i)
  simpa [Complex.mul_conj, Complex.normSq_apply] using h

theorem norm_entry_le_one (U : UnitaryGroup α) (i j : α) : ‖U i j‖ ≤ 1 := by
  have h : Complex.normSq (U i j) ≤ 1 := by
    rw [← sum_normSq_row U i]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (U i j)]

/-- Compactness is proved from closedness and the entrywise unit-ball bound. -/
instance : CompactSpace (UnitaryGroup α) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_entry_le_one ⟨U, hU⟩ i j

instance : MeasurableSpace (UnitaryGroup α) := borel _
instance : BorelSpace (UnitaryGroup α) := ⟨rfl⟩

/-- Haar measure normalized on the whole compact group, hence of total mass one. -/
noncomputable def haar (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (UnitaryGroup α) := Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure (haar α) := by unfold haar; infer_instance

instance : IsProbabilityMeasure (haar α) where
  measure_univ := Measure.haarMeasure_self

/-- Uniqueness among left-invariant probability measures on this compact group. -/
theorem eq_haar (μ : Measure (UnitaryGroup α)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haar α := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ (haar α)
  have hc := congr_arg (fun ν : Measure (UnitaryGroup α) => ν Set.univ) h
  have hc' : Measure.haarScalarFactor μ (haar α) = 1 := by
    simpa [ENNReal.smul_def, smul_eq_mul] using hc.symm
  simpa [hc'] using h

instance : (haar α).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    letI := Measure.isProbabilityMeasure_map (μ := haar α) (measurable_mul_const g).aemeasurable
    exact eq_haar _

instance : (haar α).IsInvInvariant where
  inv_eq_self := by
    letI : IsProbabilityMeasure (haar α).inv :=
      Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    exact eq_haar _

end Weingarten
