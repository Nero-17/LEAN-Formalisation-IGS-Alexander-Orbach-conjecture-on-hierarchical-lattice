import IGSIII34.Percolation.ResistanceExponent
import IGSIII34.Probability.ReciprocalMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability Filter
open IGSIII.Chemical.Substitution
open scoped _root_.Topology NNReal ENNReal

theorem normalizedPhysicalResistance_moment_log_tendsto_zero
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (exponent : ℝ) :
    Tendsto (fun depth : ℕ => Real.log (∫ marks,
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 0) := by
  apply moment_log_div_nat_tendsto_zero_of_uniform_real_moments _ _
    (fun depth => NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth))
    (fun depth marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks).property)
    _ (normalizedPhysicalResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint) exponent
  intro depth
  filter_upwards [normalizedPhysicalResistance_positive_ae rule classical parameter positive belowOne fixedPoint depth] with marks valuePositive
  exact_mod_cast valuePositive

theorem electricalIteration_moment_log_decomposition
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) (exponent : ℝ) :
    Real.log (∫ marks, (electricalIteration rule marks depth [])^exponent
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      exponent * Real.log (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) +
        Real.log (∫ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  obtain ⟨bound, bounds⟩ := normalizedPhysicalResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint exponent
  have momentPositive : 0 < ∫ marks,
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
    obtain ⟨inverseBound, inverseBounds⟩ := normalizedPhysicalResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint (-exponent)
    have reciprocalIntegrable : Integrable (fun marks =>
        ((normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent)⁻¹)
          (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
      apply (inverseBounds depth).1.congr
      filter_upwards with marks
      exact Real.rpow_neg (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks).property exponent
    have productBound := integral_mul_reciprocal_integral_ge_one
      (independentInnovationLaw rule parameter positive belowOne fixedPoint)
      (fun marks => (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent)
      ((NNReal.continuous_coe.measurable.comp (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth)).pow measurable_const)
      (by
        filter_upwards [normalizedPhysicalResistance_positive_ae rule classical parameter positive belowOne fixedPoint depth] with marks valuePositive
        apply Real.rpow_pos_of_pos _ exponent
        exact_mod_cast valuePositive)
      (bounds depth).1 reciprocalIntegrable
    have meanNonnegative : 0 ≤ ∫ marks,
        (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint :=
      integral_nonneg (fun marks => Real.rpow_nonneg (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks).property exponent)
    by_contra notPositive
    have meanZero := le_antisymm (le_of_not_gt notPositive) meanNonnegative
    rw [meanZero, zero_mul] at productBound
    norm_num at productBound
  have scalePositive : 0 < (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) := by
    exact_mod_cast electricalOrbitScale_positive rule classical parameter positive belowOne fixedPoint depth
  have momentIdentity : (∫ marks, (electricalIteration rule marks depth [])^exponent
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ)^exponent *
        ∫ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)^exponent
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with marks
    have equality := congrArg (fun value : ℝ≥0 => (value : ℝ))
      (electricalIteration_eq_scale_mul_normalized rule classical parameter positive belowOne fixedPoint depth marks)
    change electricalIteration rule marks depth [] =
      (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) *
        (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ) at equality
    rw [equality]
    exact Real.mul_rpow scalePositive.le (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks).property
  rw [momentIdentity, Real.log_mul (Real.rpow_pos_of_pos scalePositive exponent).ne' momentPositive.ne',
    Real.log_rpow scalePositive]

theorem electricalIteration_moment_log_limit_of_mean_log_limit
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (growth exponent : ℝ)
    (meanLimit : Tendsto (fun depth : ℕ => Real.log (∫ marks, electricalIteration rule marks depth []
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth))) :
    Tendsto (fun depth : ℕ => Real.log (∫ marks, (electricalIteration rule marks depth [])^exponent
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (exponent*Real.log growth)) := by
  have scaleLimit : Tendsto (fun depth : ℕ =>
      Real.log (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ)/depth) atTop (𝓝 (Real.log growth)) := by
    simpa only [electricalOrbitScale_eq_actual_mean rule classical parameter positive belowOne fixedPoint] using meanLimit
  have normalizedLimit := normalizedPhysicalResistance_moment_log_tendsto_zero rule classical parameter positive belowOne fixedPoint exponent
  have result := (scaleLimit.const_mul exponent).add normalizedLimit
  simp only [add_zero] at result
  apply result.congr'
  filter_upwards with depth
  rw [electricalIteration_moment_log_decomposition rule classical parameter positive belowOne fixedPoint depth exponent,
    add_div, mul_div_assoc]

theorem exists_actual_electrical_exponent
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
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth)) ∧
      ∀ exponent : ℝ, Tendsto (fun depth : ℕ => Real.log (∫ marks, (electricalIteration rule marks depth [])^exponent
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (exponent*Real.log growth)) := by
  obtain ⟨growth, aboveOne, lower, upper, almostSure, meanLimit, meanLogLimit⟩ :=
    exists_actual_electrical_log_exponent rule classical parameter positive belowOne fixedPoint pathLength distanceBound
  exact ⟨growth, aboveOne, lower, upper, almostSure, meanLimit, meanLogLimit,
    fun exponent => electricalIteration_moment_log_limit_of_mean_log_limit rule classical parameter positive belowOne fixedPoint growth exponent meanLimit⟩

end
end IGSIII34.Percolation
