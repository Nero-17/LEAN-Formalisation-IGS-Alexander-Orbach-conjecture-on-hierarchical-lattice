import IGSIII34.Probability.MomentFamily
import IGSIII34.Probability.InvariantBounds
import IGSIII34.Percolation.HighMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII34.Probability _root_.Topology
open scoped NNReal ENNReal

theorem normalizedElectricalLaw_preserves_momentFamily
    (rule : Rule) (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (coefficient : ℝ≥0) (coefficientPositive : 0 < coefficient)
    (coefficientBelow : (coefficient : ℝ) ≤ deriv rule.network.reliability parameter)
    (lowerOrder : ℕ) (lowerOrderAtLeastTwo : 2 ≤ lowerOrder) (bounds : ℕ → ℝ≥0)
    (boundsProperties : ∀ power, lowerOrder ≤ power → 1 ≤ bounds power ∧
      ((coefficient : ℝ≥0∞) ^ power)⁻¹ *
        ((rule.edges : ℝ≥0∞) * bounds power + (rule.edges : ℝ≥0∞) ^ power *
          (bounds power : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) ≤ bounds power)
    (law : ProbabilityMeasure ℝ≥0) (member : law ∈ meanOneMomentFamily lowerOrder bounds) :
    normalizedElectricalLaw rule parameter positive belowOne fixedPoint law ∈
      meanOneMomentFamily lowerOrder bounds := by
  have meanOne := lintegral_eq_one_of_mean_eq_one law member.1
  have secondMomentBound := meanOneMomentFamily_secondMoment_bound
    lowerOrder bounds lowerOrderAtLeastTwo law member
  have meanLower : (coefficient : ℝ) ≤ electricalOutputMean rule parameter positive belowOne fixedPoint law :=
    coefficientBelow.trans (electricalOutputMean_pivotal_lower rule parameter positive belowOne fixedPoint
      law (1 + bounds lowerOrder) secondMomentBound meanOne)
  have coefficientPositive' : (0 : ℝ) < coefficient := by exact_mod_cast coefficientPositive
  constructor
  · exact normalizedElectricalLaw_mean rule parameter positive belowOne fixedPoint law
      (coefficientPositive'.trans_le meanLower)
  · intro power orderBound
    exact (normalizedElectricalLaw_powerMoment_bound rule parameter positive belowOne fixedPoint law
      (lowerOrderAtLeastTwo.trans orderBound) (bounds power) (boundsProperties power orderBound).1
      (member.2 power orderBound) meanOne coefficient coefficientPositive meanLower).trans
        (boundsProperties power orderBound).2

theorem exists_nonnegative_electrical_eigenlaw (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ law : ProbabilityMeasure ℝ≥0,
      (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1 ∧
      (∀ power : ℕ, (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) < ∞) ∧
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law ∧
      1 < electricalOutputMean rule parameter positive belowOne fixedPoint law := by
  have derivativeAboveOne : 1 < deriv rule.network.reliability parameter :=
    rule.network.interior_fixed_point_strictly_unstable parameter positive belowOne fixedPoint classical.scale
  let coefficient : ℝ≥0 := Real.toNNReal (deriv rule.network.reliability parameter)
  have coefficientEquality : (coefficient : ℝ) = deriv rule.network.reliability parameter :=
    Real.coe_toNNReal _ (zero_lt_one.trans derivativeAboveOne).le
  have coefficientAboveOne : 1 < coefficient := by
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_one, coefficientEquality] using derivativeAboveOne
  obtain ⟨lowerOrder, lowerOrderAtLeastTwo, bounds, boundsProperties⟩ :=
    exists_all_invariant_powerMoment_bounds rule.edges coefficient coefficientAboveOne
  let family := meanOneMomentFamily lowerOrder bounds
  have meanPositive : ∀ law ∈ family,
      0 < electricalOutputMean rule parameter positive belowOne fixedPoint law := by
    intro law member
    exact electricalOutputMean_positive_of_classical rule classical parameter positive belowOne fixedPoint
      law (1 + bounds lowerOrder)
      (meanOneMomentFamily_secondMoment_bound lowerOrder bounds lowerOrderAtLeastTwo law member)
      (lintegral_eq_one_of_mean_eq_one law member.1)
  have continuousMap : Continuous (fun law : family =>
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint law.val) :=
    normalizedElectricalLaw_continuous_on_family rule parameter positive belowOne fixedPoint
      (1 + bounds lowerOrder) family
      (meanOneMomentFamily_secondMoment_bound lowerOrder bounds lowerOrderAtLeastTwo) meanPositive
  let map : C(family, family) :=
    ⟨fun law => ⟨normalizedElectricalLaw rule parameter positive belowOne fixedPoint law.val,
      normalizedElectricalLaw_preserves_momentFamily rule parameter positive belowOne fixedPoint coefficient
        (zero_lt_one.trans coefficientAboveOne) coefficientEquality.le lowerOrder lowerOrderAtLeastTwo bounds
        boundsProperties law.val law.property⟩, continuousMap.subtype_mk _⟩
  obtain ⟨law, fixed⟩ := probability_schauder_fixed_point family
    (isCompact_meanOneMomentFamily lowerOrder bounds lowerOrderAtLeastTwo)
    (meanOneMomentFamily_nonempty lowerOrder bounds (fun power orderBound => (boundsProperties power orderBound).1))
    (fun first firstMember second secondMember firstWeight secondWeight weightsSum =>
      meanOneMomentFamily_mixture_closed lowerOrder bounds first second firstMember secondMember
        firstWeight secondWeight weightsSum) map
  refine ⟨law.val, law.property.1,
    meanOneMomentFamily_all_moments_finite lowerOrder bounds law.val law.property,
    congrArg Subtype.val fixed, ?_⟩
  exact derivativeAboveOne.trans_le (electricalOutputMean_pivotal_lower rule parameter positive belowOne fixedPoint
    law.val (1 + bounds lowerOrder)
    (meanOneMomentFamily_secondMoment_bound lowerOrder bounds lowerOrderAtLeastTwo law.val law.property)
    (lintegral_eq_one_of_mean_eq_one law.val law.property.1))

end
end IGSIII34.Percolation
