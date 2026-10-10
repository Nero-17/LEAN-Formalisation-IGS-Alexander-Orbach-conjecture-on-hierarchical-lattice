import IGSIII34.Probability.ConvexLaws
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Probability
noncomputable section
open MeasureTheory BoundedContinuousFunction Filter Set _root_.Topology
open scoped NNReal ENNReal

variable {Outcome : Type*} [TopologicalSpace Outcome] [MeasurableSpace Outcome]
  [BorelSpace Outcome] [HasOuterApproxClosed Outcome]

def boundedTruncation (response : Outcome → ℝ≥0) (responseContinuous : Continuous response)
    (bound : ℕ) : Outcome →ᵇ ℝ≥0 where
  toFun outcome := min (response outcome) (bound : ℝ≥0)
  continuous_toFun := responseContinuous.min continuous_const
  map_bounded' := by
    refine ⟨bound, ?_⟩
    intro first second
    rw [NNReal.dist_eq]
    apply abs_sub_le_iff.mpr
    constructor
    · have boundFirst : ((min (response first) (bound : ℝ≥0) : ℝ≥0) : ℝ) ≤ bound := by
        exact_mod_cast min_le_right (response first) (bound : ℝ≥0)
      linarith [NNReal.coe_nonneg (min (response second) (bound : ℝ≥0))]
    · have boundSecond : ((min (response second) (bound : ℝ≥0) : ℝ≥0) : ℝ) ≤ bound := by
        exact_mod_cast min_le_right (response second) (bound : ℝ≥0)
      linarith [NNReal.coe_nonneg (min (response first) (bound : ℝ≥0))]

theorem lintegral_eq_iSup_boundedTruncation (law : ProbabilityMeasure Outcome)
    (response : Outcome → ℝ≥0) (responseContinuous : Continuous response) :
    (∫⁻ outcome, (response outcome : ℝ≥0∞) ∂(law : Measure Outcome)) =
      ⨆ bound : ℕ, ∫⁻ outcome,
        (boundedTruncation response responseContinuous bound outcome : ℝ≥0∞) ∂(law : Measure Outcome) := by
  rw [← lintegral_iSup]
  · congr 1
    funext outcome
    change (response outcome : ℝ≥0∞) = ⨆ bound : ℕ, (min (response outcome) (bound : ℝ≥0) : ℝ≥0∞)
    simp only [ENNReal.coe_min, ENNReal.coe_natCast]
    change (response outcome : ℝ≥0∞) = ⨆ bound : ℕ, (response outcome : ℝ≥0∞) ⊓ bound
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  · intro bound
    exact (boundedTruncation response responseContinuous bound).continuous.measurable.coe_nnreal_ennreal
  · intro first second comparison outcome
    change (min (response outcome) (first : ℝ≥0) : ℝ≥0∞) ≤
      (min (response outcome) (second : ℝ≥0) : ℝ≥0∞)
    exact ENNReal.coe_le_coe.mpr (min_le_min_left _ (by exact_mod_cast comparison))

theorem isClosed_lintegral_sublevel (response : Outcome → ℝ≥0)
    (responseContinuous : Continuous response) (bound : ℝ≥0∞) :
    IsClosed {law : ProbabilityMeasure Outcome |
      (∫⁻ outcome, (response outcome : ℝ≥0∞) ∂(law : Measure Outcome)) ≤ bound} := by
  have setEquality :
      {law : ProbabilityMeasure Outcome |
        (∫⁻ outcome, (response outcome : ℝ≥0∞) ∂(law : Measure Outcome)) ≤ bound} =
      ⋂ truncation : ℕ, {law : ProbabilityMeasure Outcome |
        (∫⁻ outcome, (boundedTruncation response responseContinuous truncation outcome : ℝ≥0∞)
          ∂(law : Measure Outcome)) ≤ bound} := by
    ext law
    simp only [Set.mem_setOf_eq, Set.mem_iInter,
      lintegral_eq_iSup_boundedTruncation law response responseContinuous, iSup_le_iff]
  rw [setEquality]
  apply isClosed_iInter
  intro truncation
  exact isClosed_le (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
    (boundedTruncation response responseContinuous truncation)) continuous_const

theorem lintegral_probabilityMixture (first second : ProbabilityMeasure Outcome)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1)
    (response : Outcome → ℝ≥0∞) :
    (∫⁻ outcome, response outcome
      ∂(probabilityMixture first second firstWeight secondWeight weightsSum : Measure Outcome)) =
      (firstWeight : ℝ≥0∞) * (∫⁻ outcome, response outcome ∂(first : Measure Outcome)) +
      (secondWeight : ℝ≥0∞) * (∫⁻ outcome, response outcome ∂(second : Measure Outcome)) := by
  change (∫⁻ outcome, response outcome ∂(firstWeight • (first : Measure Outcome) +
    secondWeight • (second : Measure Outcome))) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

theorem probabilityMixture_lintegral_le (first second : ProbabilityMeasure Outcome)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1)
    (response : Outcome → ℝ≥0∞) {bound : ℝ≥0∞}
    (firstBound : (∫⁻ outcome, response outcome ∂(first : Measure Outcome)) ≤ bound)
    (secondBound : (∫⁻ outcome, response outcome ∂(second : Measure Outcome)) ≤ bound) :
    (∫⁻ outcome, response outcome
      ∂(probabilityMixture first second firstWeight secondWeight weightsSum : Measure Outcome)) ≤ bound := by
  rw [lintegral_probabilityMixture]
  calc
    _ ≤ (firstWeight : ℝ≥0∞) * bound + (secondWeight : ℝ≥0∞) * bound :=
      add_le_add (mul_le_mul_left' firstBound _) (mul_le_mul_left' secondBound _)
    _ = bound := by rw [← add_mul, ← ENNReal.coe_add, weightsSum, ENNReal.coe_one, one_mul]

theorem firstMoment_sublevel_isTight (bound : ℝ≥0) :
    IsTightMeasureSet ((fun law : ProbabilityMeasure ℝ≥0 => (law : Measure ℝ≥0)) ''
      {law : ProbabilityMeasure ℝ≥0 |
        (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) ≤ bound}) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon epsilonPositive
  obtain ⟨small, smallPositive, smallBelow⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp epsilonPositive
  have smallPositive' : 0 < small := by exact_mod_cast smallPositive
  let radius : ℝ≥0 := bound / small + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have quotientBound : bound / radius ≤ small := by
    apply (div_le_iff₀ radiusPositive).mpr
    have cancel : small * (bound / small) = bound := by field_simp [smallPositive'.ne']
    dsimp [radius]
    rw [mul_add, cancel, mul_one]
    exact le_add_of_nonneg_right small.2
  refine ⟨Set.Icc 0 radius, isCompact_Icc, ?_⟩
  rintro measure ⟨law, momentBound, rfl⟩
  have radiusNotZero : (radius : ℝ≥0∞) ≠ 0 := by exact_mod_cast radiusPositive.ne'
  calc
    (law : Measure ℝ≥0) (Set.Icc 0 radius)ᶜ ≤
        (law : Measure ℝ≥0) {value : ℝ≥0 | (radius : ℝ≥0∞) ≤ value} := by
      apply measure_mono
      intro value outside
      have large : radius < value := by simpa only [Set.mem_compl_iff, Set.mem_Icc,
        zero_le, true_and, not_le] using outside
      exact ENNReal.coe_le_coe.mpr large.le
    _ ≤ (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) / radius :=
      meas_ge_le_lintegral_div measurable_id.coe_nnreal_ennreal.aemeasurable radiusNotZero ENNReal.coe_ne_top
    _ ≤ (bound : ℝ≥0∞) / radius := ENNReal.div_le_div_right momentBound _
    _ ≤ small := by
      rw [← ENNReal.coe_div radiusPositive.ne']
      exact ENNReal.coe_le_coe.mpr quotientBound
    _ ≤ epsilon := smallBelow.le

theorem isCompact_firstMoment_sublevel (bound : ℝ≥0) :
    IsCompact {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) ≤ bound} := by
  have tight := firstMoment_sublevel_isTight bound
  have compactClosure := isCompact_closure_of_isTightMeasureSet tight
  have closed := isClosed_lintegral_sublevel (fun value : ℝ≥0 => value) continuous_id bound
  simpa only [closed.closure_eq] using compactClosure

end
end IGSIII34.Probability
