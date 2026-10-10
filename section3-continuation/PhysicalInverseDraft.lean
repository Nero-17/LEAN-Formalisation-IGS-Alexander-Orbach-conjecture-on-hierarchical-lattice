import IGSIII34.Percolation.PhysicalMoments
import IGSIII34.Percolation.OrbitTail
import IGSIII34.Probability.UniformInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

theorem normalizedElectricalOrbit_uniform_inverse_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun value : ℝ≥0 => (value : ℝ)⁻¹ ^ power)
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) ∧
      (∫ value : ℝ≥0, (value : ℝ)⁻¹ ^ power
        ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) ≤ bound := by
  obtain ⟨start, startNonnegative, startBelowOne, tailBound⟩ :=
    normalizedElectricalOrbit_uniform_thinning_tail rule classical parameter positive belowOne fixedPoint
  have baseAboveOne : 1 < (rule.edges : ℝ)^2 + 1 := by
    obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classical.connected _)
    have edgesPositive : (0 : ℝ) < rule.edges := by exact_mod_cast Nat.zero_lt_of_lt edge.isLt
    nlinarith
  refine ⟨(1 / 2 : ℝ)⁻¹ ^ power * (1 + ((rule.edges : ℝ)^2+1)^power *
    ∑' scale : ℕ, (((rule.edges : ℝ)^2+1)^power)^scale *
      (thinningMap rule.network parameter)^[scale] start), fun depth => ?_⟩
  apply inverse_moment_of_uniform_thinning_tail_ae rule.network
    (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) power
    NNReal.continuous_coe.measurable _ positive belowOne fixedPoint classical.scale
    startNonnegative startBelowOne baseAboveOne (by norm_num) (tailBound depth)
  filter_upwards [normalizedElectricalOrbit_positive_ae rule classical parameter positive belowOne fixedPoint depth]
    with value valuePositive
  exact_mod_cast valuePositive

theorem normalizedPhysicalResistance_uniform_inverse_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)⁻¹ ^ power)
        (independentInnovationLaw rule parameter positive belowOne fixedPoint) ∧
      (∫ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)⁻¹ ^ power
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_inverse_moment
    rule classical parameter positive belowOne fixedPoint power
  refine ⟨bound, fun depth => ?_⟩
  have mapped := integral_map (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint)
    (φ := normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth)
    (f := fun value : ℝ≥0 => (value : ℝ)⁻¹ ^ power)
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable
    (NNReal.continuous_coe.measurable.inv.pow_const power).aestronglyMeasurable
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth] at mapped
  refine ⟨?_, mapped.symm.trans_le (momentBound depth).2⟩
  apply (integrable_map_measure (NNReal.continuous_coe.measurable.inv.pow_const power).aestronglyMeasurable
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable).mp
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth]
  exact (momentBound depth).1

theorem normalizedElectricalOrbit_uniform_natural_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun value : ℝ≥0 => (value : ℝ)^power)
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) ∧
      (∫ value : ℝ≥0, (value : ℝ)^power
        ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_moment rule classical parameter positive belowOne fixedPoint power
  refine ⟨bound, fun depth => ⟨integrable_nnreal_power_of_lintegral_finite _ power
    ((momentBound depth).trans_lt ENNReal.coe_lt_top), ?_⟩⟩
  have result := integral_coe_le_of_lintegral_coe_le (f := fun value : ℝ≥0 => value^power)
    (b := bound) (by simpa only [ENNReal.coe_pow] using momentBound depth)
  simpa only [NNReal.coe_pow] using result

theorem normalizedElectricalOrbit_uniform_real_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (exponent : ℝ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun value : ℝ≥0 => (value : ℝ)^exponent)
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) ∧
      (∫ value : ℝ≥0, (value : ℝ)^exponent
        ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) ≤ bound := by
  by_cases nonnegative : 0 ≤ exponent
  · obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
    obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_natural_moment
      rule classical parameter positive belowOne fixedPoint power
    refine ⟨1 + bound, fun depth => ⟨?_, ?_⟩⟩
    · exact integrable_rpow_of_nat_moments _ NNReal.continuous_coe.measurable (fun value => value.property)
        (fun power => (Classical.choose_spec (normalizedElectricalOrbit_uniform_natural_moment
          rule classical parameter positive belowOne fixedPoint power) depth).1) nonnegative
    · exact (IGSIII.Chemical.SmallBall.integral_rpow_le_one_add_integral_pow _
        NNReal.continuous_coe.measurable (fun value => value.property)
        nonnegative exponentBound (momentBound depth).1).trans (add_le_add le_rfl (momentBound depth).2)
  · obtain ⟨power, exponentBound⟩ := exists_nat_ge (-exponent)
    obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_inverse_moment
      rule classical parameter positive belowOne fixedPoint power
    refine ⟨1 + bound, fun depth => ?_⟩
    have inverseIntegrable := integrable_rpow_of_nat_moments
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)
      NNReal.continuous_coe.measurable.inv (fun value => inv_nonneg.mpr value.property)
      (fun power => (Classical.choose_spec (normalizedElectricalOrbit_uniform_inverse_moment
        rule classical parameter positive belowOne fixedPoint power) depth).1)
      (neg_nonneg.mpr (le_of_not_ge nonnegative))
    have inverseBound := (IGSIII.Chemical.SmallBall.integral_rpow_le_one_add_integral_pow _
      NNReal.continuous_coe.measurable.inv (fun value => inv_nonneg.mpr value.property)
      (neg_nonneg.mpr (le_of_not_ge nonnegative)) exponentBound (momentBound depth).1).trans
      (add_le_add le_rfl (momentBound depth).2)
    have exponentEquality : (fun value : ℝ≥0 => (value : ℝ)^exponent) =
        fun value : ℝ≥0 => ((value : ℝ)⁻¹)^(-exponent) := by
      funext value
      rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]
    rw [exponentEquality]
    exact ⟨inverseIntegrable, inverseBound⟩

theorem normalizedPhysicalResistance_eq_div_actual_mean (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ) =
      electricalIteration rule marks depth [] /
        (∫ sample, electricalIteration rule sample depth []
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  rw [← electricalOrbitScale_eq_actual_mean rule classical parameter positive belowOne fixedPoint depth]
  change (((electricalOrbitScale rule parameter positive belowOne fixedPoint depth)⁻¹ *
    electricalIterationNNReal rule marks depth [] : ℝ≥0) : ℝ) = _
  simp only [NNReal.coe_mul, NNReal.coe_inv, electricalIterationNNReal]
  rw [div_eq_mul_inv, mul_comm]
  rfl

theorem normalizedPhysicalResistance_uniform_real_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (exponent : ℝ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent)
        (independentInnovationLaw rule parameter positive belowOne fixedPoint) ∧
      (∫ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_real_moment
    rule classical parameter positive belowOne fixedPoint exponent
  refine ⟨bound, fun depth => ?_⟩
  have responseMeasurable : Measurable (fun value : ℝ≥0 => (value : ℝ)^exponent) :=
    NNReal.continuous_coe.measurable.pow measurable_const
  have mapped := integral_map (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint)
    (φ := normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth)
    (f := fun value : ℝ≥0 => (value : ℝ)^exponent)
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable
    responseMeasurable.aestronglyMeasurable
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth] at mapped
  refine ⟨?_, mapped.symm.trans_le (momentBound depth).2⟩
  apply (integrable_map_measure responseMeasurable.aestronglyMeasurable
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable).mp
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth]
  exact (momentBound depth).1

end
end IGSIII34.Percolation
