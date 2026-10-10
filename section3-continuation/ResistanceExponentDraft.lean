import IGSIII34.Percolation.GenerationMean
import IGSIII34.Probability.LogMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability Filter
open IGSIII.Chemical.Substitution
open scoped _root_.Topology NNReal ENNReal

theorem normalizedPhysicalResistance_uniform_log_square
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ))^2)
        (independentInnovationLaw rule parameter positive belowOne fixedPoint) ∧
      (∫ marks, (Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ))^2
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨positiveMoment, positiveBounds⟩ := normalizedPhysicalResistance_uniform_real_moment
    rule classical parameter positive belowOne fixedPoint 2
  obtain ⟨inverseMoment, inverseBounds⟩ := normalizedPhysicalResistance_uniform_inverse_moment
    rule classical parameter positive belowOne fixedPoint 2
  refine ⟨2*(positiveMoment+inverseMoment), ?_⟩
  apply uniform_log_second_moment _
    (fun depth marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ))
    (fun depth => NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth))
    (fun depth marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks).property)
    positiveMoment inverseMoment _ inverseBounds
  intro depth
  simpa only [Real.rpow_two] using positiveBounds depth

theorem normalizedPhysicalResistance_log_div_nat_tendsto_zero_ae
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      Tendsto (fun depth : ℕ => Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)/depth)
        atTop (𝓝 0) := by
  obtain ⟨bound, bounds⟩ := normalizedPhysicalResistance_uniform_log_square rule classical parameter positive belowOne fixedPoint
  exact ae_log_div_nat_tendsto_zero_of_uniform_second_moment _ _
    (fun depth => NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth))
    bound bounds

theorem electricalIteration_log_eq_mean_add_normalized_log_ae
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (fun marks => Real.log (electricalIteration rule marks depth [])) =ᵐ[independentInnovationLaw rule parameter positive belowOne fixedPoint]
      (fun marks => Real.log (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) +
        Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)) := by
  filter_upwards [normalizedPhysicalResistance_positive_ae rule classical parameter positive belowOne fixedPoint depth] with marks normalizedPositive
  have scalePositive : 0 < (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) := by
    exact_mod_cast electricalOrbitScale_positive rule classical parameter positive belowOne fixedPoint depth
  have inputPositive : 0 < (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ) := by
    exact_mod_cast normalizedPositive
  have equality := congrArg (fun value : ℝ≥0 => (value : ℝ))
    (electricalIteration_eq_scale_mul_normalized rule classical parameter positive belowOne fixedPoint depth marks)
  change electricalIteration rule marks depth [] =
    (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) *
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ) at equality
  rw [equality, Real.log_mul scalePositive.ne' inputPositive.ne']

theorem electricalIteration_mean_log_decomposition
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    Integrable (fun marks => Real.log (electricalIteration rule marks depth []))
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) ∧
    (∫ marks, Real.log (electricalIteration rule marks depth [])
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      Real.log (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) +
        ∫ marks, Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
  obtain ⟨bound, bounds⟩ := normalizedPhysicalResistance_uniform_log_square rule classical parameter positive belowOne fixedPoint
  have normalizedIntegrable : Integrable (fun marks => Real.log
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ))
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := (integral_log_abs_bound_of_second_moment _ _
    (NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth))
    (bounds depth).1).1
  have equality := electricalIteration_log_eq_mean_add_normalized_log_ae rule classical parameter positive belowOne fixedPoint depth
  refine ⟨((integrable_const _).add normalizedIntegrable).congr equality.symm, ?_⟩
  rw [integral_congr_ae equality, integral_add (integrable_const _) normalizedIntegrable]
  simp

theorem exists_actual_electrical_log_exponent
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ growth : ℝ, 1 < growth ∧ deriv rule.network.reliability parameter ≤ growth ∧
      growth ≤ (∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _)) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
        Tendsto (fun depth : ℕ => Real.log (electricalIteration rule marks depth [])/depth) atTop (𝓝 (Real.log growth))) ∧
      Tendsto (fun depth : ℕ => Real.log (∫ marks, electricalIteration rule marks depth []
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth)) ∧
      Tendsto (fun depth : ℕ => (∫ marks, Real.log (electricalIteration rule marks depth [])
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth)) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, lower, upper, bounds⟩ :=
    exists_actual_electrical_growth rule classical parameter positive belowOne fixedPoint pathLength distanceBound
  have growthAboveOne := (rule.network.interior_fixed_point_strictly_unstable parameter positive belowOne fixedPoint classical.scale).trans_le lower
  have scaleLimit := tendsto_log_div_nat_of_growth_bounds
    (fun depth => (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ)) growth constant⁻¹
    (zero_lt_one.trans growthAboveOne) (one_le_inv₀ constantPositive |>.mpr constantAtMostOne) bounds
  refine ⟨growth, growthAboveOne, lower, upper, ?_, ?_, ?_⟩
  · have allLogIdentities := ae_all_iff.mpr (fun depth =>
      electricalIteration_log_eq_mean_add_normalized_log_ae rule classical parameter positive belowOne fixedPoint depth)
    filter_upwards [allLogIdentities,
      normalizedPhysicalResistance_log_div_nat_tendsto_zero_ae rule classical parameter positive belowOne fixedPoint]
      with marks identities normalizedLimit
    have result := scaleLimit.add normalizedLimit
    simp only [add_zero] at result
    apply result.congr'
    filter_upwards with depth
    rw [identities depth, add_div]
  · simpa only [← electricalOrbitScale_eq_actual_mean rule classical parameter positive belowOne fixedPoint] using scaleLimit
  · obtain ⟨bound, logSquares⟩ := normalizedPhysicalResistance_uniform_log_square rule classical parameter positive belowOne fixedPoint
    have integralBounds (depth : ℕ) :
        |∫ marks, Real.log (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint| ≤ 1+bound := by
      exact (integral_log_abs_bound_of_second_moment _ _
        (NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth))
        (logSquares depth).1).2.trans (add_le_add le_rfl (logSquares depth).2)
    have normalizedLimit := tendsto_div_nat_of_bounded _ (1+bound) integralBounds
    have result := scaleLimit.add normalizedLimit
    simp only [add_zero] at result
    apply result.congr'
    filter_upwards with depth
    rw [(electricalIteration_mean_log_decomposition rule classical parameter positive belowOne fixedPoint depth).2, add_div]

end
end IGSIII34.Percolation
