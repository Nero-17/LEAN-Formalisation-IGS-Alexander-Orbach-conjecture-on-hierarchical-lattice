import IGSIII.Probability.CompactApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compact balls in the actual finite-factor subspace of Lp. -/

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory
open scoped ENNReal

variable {Sample Tag : Type*} [MeasurableSpace Sample] [MeasurableSpace Tag]
    [Fintype Tag] [MeasurableSingletonClass Tag]
    (measure : Measure Sample) [IsFiniteMeasure measure]
    (order : ℝ≥0∞) [Fact (1 ≤ order)]
    (factor : Sample → Tag) (factorMeasurable : Measurable factor)

noncomputable def factorIndicator (tag : Tag) : Lp ℝ order measure :=
  ((memLp_const (μ := measure) (p := order) (1 : ℝ)).indicator
    (factorMeasurable (measurableSet_singleton tag))).toLp
      ((factor ⁻¹' {tag}).indicator (fun _ => (1 : ℝ)))

noncomputable def factorLinearMap : (Tag → ℝ) →ₗ[ℝ] Lp ℝ order measure where
  toFun coefficient := ∑ tag, coefficient tag • factorIndicator measure order factor factorMeasurable tag
  map_add' first second := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar coefficient := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

noncomputable def factorBall (bound : ℝ) : Set (Lp ℝ order measure) :=
  {value | value ∈ (factorLinearMap measure order factor factorMeasurable).range ∧ ‖value‖ ≤ bound}

theorem factorBall_compact (bound : ℝ) :
    IsCompact (factorBall measure order factor factorMeasurable bound) := by
  let subspace := (factorLinearMap measure order factor factorMeasurable).range
  have compact : IsCompact (Metric.closedBall (0 : subspace) bound) := isCompact_closedBall _ _
  have image : (Subtype.val '' Metric.closedBall (0 : subspace) bound) =
      factorBall measure order factor factorMeasurable bound := by
    ext value
    constructor
    · rintro ⟨point, member, rfl⟩
      exact ⟨point.property, by simpa [Metric.mem_closedBall, dist_eq_norm] using member⟩
    · rintro ⟨member, bounded⟩
      exact ⟨⟨value, member⟩, by simpa [Metric.mem_closedBall, dist_eq_norm] using bounded, rfl⟩
  rw [← image]
  exact compact.image continuous_subtype_val

theorem factorLinearMap_mem_ball (coefficient : Tag → ℝ) (bound : ℝ)
    (bounded : ‖factorLinearMap measure order factor factorMeasurable coefficient‖ ≤ bound) :
    factorLinearMap measure order factor factorMeasurable coefficient ∈
      factorBall measure order factor factorMeasurable bound :=
  ⟨⟨coefficient, rfl⟩, bounded⟩


theorem factorIndicator_coe_ae (tag : Tag) :
    ⇑(factorIndicator measure order factor factorMeasurable tag) =ᵐ[measure]
      (factor ⁻¹' {tag}).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

theorem factorLinearMap_coe_ae (coefficient : Tag → ℝ) :
    ⇑(factorLinearMap measure order factor factorMeasurable coefficient) =ᵐ[measure]
      coefficient ∘ factor := by
  classical
  have components : ∀ tag : Tag,
      ⇑(coefficient tag • factorIndicator measure order factor factorMeasurable tag) =ᵐ[measure]
        fun sample => coefficient tag * (factor ⁻¹' {tag}).indicator (fun _ => (1 : ℝ)) sample := by
    intro tag
    filter_upwards [Lp.coeFn_smul (coefficient tag) (factorIndicator measure order factor factorMeasurable tag),
      factorIndicator_coe_ae measure order factor factorMeasurable tag] with sample scalarEqual indicatorEqual
    simp only [scalarEqual, Pi.smul_apply, smul_eq_mul, indicatorEqual]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun tag => coefficient tag • factorIndicator measure order factor factorMeasurable tag),
    ae_all_iff.mpr components] with sample sumEqual termsEqual
  change (∑ tag, coefficient tag • factorIndicator measure order factor factorMeasurable tag) sample = _
  rw [sumEqual]
  simp_rw [termsEqual]
  simp [Set.indicator_apply, Function.comp_apply, eq_comm]

theorem mem_factor_range_of_coe_ae
    (value : Lp ℝ order measure) (coefficient : Tag → ℝ)
    (represented : ⇑value =ᵐ[measure] coefficient ∘ factor) :
    value ∈ (factorLinearMap measure order factor factorMeasurable).range := by
  refine ⟨coefficient, ?_⟩
  apply Lp.ext
  exact (factorLinearMap_coe_ae measure order factor factorMeasurable coefficient).trans represented.symm

theorem mem_factorBall_of_coe_ae
    (value : Lp ℝ order measure) (coefficient : Tag → ℝ) (bound : ℝ)
    (represented : ⇑value =ᵐ[measure] coefficient ∘ factor) (bounded : ‖value‖ ≤ bound) :
    value ∈ factorBall measure order factor factorMeasurable bound :=
  ⟨mem_factor_range_of_coe_ae measure order factor factorMeasurable value coefficient represented, bounded⟩
end IGSIII.Probability


