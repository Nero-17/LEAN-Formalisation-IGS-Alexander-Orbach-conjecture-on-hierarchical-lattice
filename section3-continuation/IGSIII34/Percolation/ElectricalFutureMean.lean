import IGSIII34.Percolation.ElectricalIterateMeanComparison
import IGSIII34.Percolation.ElectricalOrbitInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory

theorem electricalComparisonCoefficient_nonnegative
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (first second : Lp ℝ 2 measure) [IsProbabilityMeasure measure]
    (secondPositive : ∀ᵐ sample ∂measure, 0 < second sample) :
    0 ≤ electricalComparisonCoefficient measure first second := by
  exact div_nonneg
    (integral_nonneg (fun sample => mul_nonneg (le_max_right _ _)
      (zero_le_one.trans (le_max_left _ _))))
    (electrical_comparison_denominator_mean_positive measure second secondPositive).le

theorem integral_abs_sub_eq_positive_parts
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (first second : Lp ℝ 2 measure) :
    (∫ sample, |first sample-second sample| ∂measure) =
      (∫ sample, max (first sample-second sample) 0 ∂measure) +
        ∫ sample, max (second sample-first sample) 0 ∂measure := by
  have firstIntegrable : Integrable (fun sample => max (first sample-second sample) 0) measure := (((Lp.memLp first).sub (Lp.memLp second)).sup
    (memLp_const (0 : ℝ))).integrable (by norm_num)
  have secondIntegrable : Integrable (fun sample => max (second sample-first sample) 0) measure := (((Lp.memLp second).sub (Lp.memLp first)).sup
    (memLp_const (0 : ℝ))).integrable (by norm_num)
  rw [← integral_add firstIntegrable secondIntegrable]
  apply integral_congr_ae
  filter_upwards [] with sample
  rcases le_total (first sample) (second sample) with comparison | comparison
  · rw [abs_of_nonpos (sub_nonpos.mpr comparison), max_eq_right (sub_nonpos.mpr comparison),
      max_eq_left (sub_nonneg.mpr comparison)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr comparison), max_eq_left (sub_nonneg.mpr comparison),
      max_eq_right (sub_nonpos.mpr comparison)]
    ring

end
end IGSIII34.Probability
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth

include classical growthPositive growthBounds in
theorem electricalOrbitLp_ae_positive (depth : ℕ) : ∀ᵐ marks ∂μ, 0 < W depth marks := by
  filter_upwards [electricalOrbitLp_above_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
      growth growthPositive (fun depth => (growthBounds depth).1) depth,
    normalizedPhysicalResistance_positive_ae rule classical p positive belowOne fixedPoint depth]
    with marks comparison physicalPositive
  have physicalPositiveReal : (0 : ℝ) < (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by
    exact_mod_cast physicalPositive
  exact physicalPositiveReal.trans_le comparison

include classical growthPositive growthBounds in
theorem electricalOrbitLp_mean_atMost (depth : ℕ) : (∫ marks, W depth marks ∂μ) ≤ constant⁻¹ := by
  rw [electricalOrbitLp_mean rule classical p positive belowOne fixedPoint growth growthPositive.le depth]
  exact (div_le_iff₀ (pow_pos growthPositive depth)).mpr (growthBounds depth).2

theorem electricalOrbitLp_iterate (depth block : ℕ) : T^[depth] (W block) = W (depth+block) := by
  exact (Function.iterate_add_apply _ depth block _).symm

include classical growthPositive growthBounds in
theorem electricalOrbit_future_absolute_mean_le
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (depth block : ℕ) :
    (∫ marks, |W (depth+1+block) marks-endpoint marks| ∂μ) ≤
      electricalComparisonCoefficient μ (W block) endpoint * (∫ marks, endpoint marks ∂μ) +
        electricalComparisonCoefficient μ endpoint (W block) * constant⁻¹ := by
  have endpointPositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth
    growthPositive (fun depth => (growthBounds depth).1) endpoint membership
  obtain ⟨orbitBound, orbitMoments⟩ := electricalOrbit_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive (fun depth => (growthBounds depth).1) 4
  obtain ⟨omegaBound, omegaMoments⟩ := electricalOmega_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive (fun depth => (growthBounds depth).1) 4
  have forward := normalized_electrical_iterate_positive_part_mean_le rule p positive belowOne fixedPoint
    growth growthPositive.le (W block) endpoint
    (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds block)
    endpointPositive (omegaMoments endpoint membership).1 depth
  have backward := normalized_electrical_iterate_positive_part_mean_le rule p positive belowOne fixedPoint
    growth growthPositive.le endpoint (W block) endpointPositive
    (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds block)
    (orbitMoments block).1 depth
  rw [Function.iterate_fixed endpointFixed, electricalOrbitLp_iterate rule p positive belowOne fixedPoint growth] at forward backward
  rw [integral_abs_sub_eq_positive_parts μ (W (depth+1+block)) endpoint]
  exact (add_le_add forward backward).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (electricalOrbitLp_mean_atMost rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds (depth+1+block))
      (electricalComparisonCoefficient_nonnegative μ endpoint (W block)
        (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds block))))

end
end IGSIII34.Percolation
