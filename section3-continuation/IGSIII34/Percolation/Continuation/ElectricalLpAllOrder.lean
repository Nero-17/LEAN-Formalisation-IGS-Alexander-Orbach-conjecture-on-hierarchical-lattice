import IGSIII34.Percolation.Continuation.ElectricalAllOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem eLpNorm_tendsto_zero_of_absolute_moments
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (sequence : ℕ → Sample → ℝ) (exponent : ℝ) (exponentPositive : 0 < exponent)
    (integrable : ∀ depth, Integrable (fun sample => |sequence depth sample|^exponent) measure)
    (convergence : Tendsto (fun depth => ∫ sample, |sequence depth sample|^exponent ∂measure) atTop (𝓝 0)) :
    Tendsto (fun depth => eLpNorm (sequence depth) (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  have formula (depth : ℕ) : eLpNorm (sequence depth) (ENNReal.ofReal exponent) measure =
      (ENNReal.ofReal (∫ sample, |sequence depth sample|^exponent ∂measure))^(1/exponent) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr exponentPositive).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal exponentPositive.le]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal (integrable depth)
      (Eventually.of_forall (fun sample => Real.rpow_nonneg (abs_nonneg _) _))]
    apply lintegral_congr
    intro sample
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) exponentPositive.le]
  simp_rw [formula]
  have result := ((ENNReal.continuous_rpow_const (y := 1/exponent)).tendsto (ENNReal.ofReal 0)).comp
    ((ENNReal.continuous_ofReal.tendsto 0).comp convergence)
  simpa only [Function.comp_def, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr exponentPositive)] using result

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_absolute_error_integrable_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (exponent : ℝ) (exponentNonnegative : 0 ≤ exponent) (depth : ℕ) :
    Integrable (fun marks => |W depth marks-endpoint marks|^exponent) μ := by
  have sequenceMoment := ((electricalOrbit_uniform_integrable_real_moment rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds exponent).choose_spec depth).1
  have endpointMoment := electricalOmega_integrable_real_moment rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds endpoint membership exponent
  apply (sequenceMoment.add endpointMoment).mono'
    ((continuous_abs.measurable.comp ((Lp.stronglyMeasurable (W depth)).measurable.sub
      (Lp.stronglyMeasurable endpoint).measurable)).pow measurable_const).aestronglyMeasurable
  filter_upwards [electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds depth,
    electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
      (fun depth => (growthBounds depth).1) endpoint membership] with marks sequencePositive endpointPositive
  change ‖|W depth marks-endpoint marks|^exponent‖ ≤ (W depth marks)^exponent+(endpoint marks)^exponent
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_sub_rpow_le_sum_of_nonnegative _ _ _ sequencePositive.le endpointPositive.le exponentNonnegative

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_eLpNorm_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Tendsto (fun depth => eLpNorm (fun marks => W depth marks-endpoint marks) (ENNReal.ofReal exponent) μ)
      atTop (𝓝 0) := by
  exact eLpNorm_tendsto_zero_of_absolute_moments μ (fun depth marks => W depth marks-endpoint marks) exponent exponentPositive
    (electricalOrbit_absolute_error_integrable_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds endpoint membership exponent exponentPositive.le)
    (electricalOrbit_absolute_error_moment_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds endpoint endpointFixed membership exponent exponentPositive)

include classical constantPositive growthPositive growthBounds in
theorem electricalIteration_eLpNorm_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (address : List (Fin rule.edges)) (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Tendsto (fun depth => eLpNorm (fun marks => growth⁻¹^depth*electricalIteration rule marks depth address-
      electricalField rule p positive belowOne fixedPoint endpoint address marks) (ENNReal.ofReal exponent) μ)
      atTop (𝓝 0) := by
  apply (electricalOrbit_eLpNorm_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    constantPositive growthPositive growthBounds endpoint endpointFixed membership exponent exponentPositive).congr'
  apply Eventually.of_forall
  intro depth
  have preserving := innovationTreeShift_preserving rule p positive belowOne fixedPoint address
  have rawMeasurable : Measurable (fun marks => growth⁻¹^depth*electricalIteration rule marks depth []-endpoint marks) :=
    (measurable_const.mul (electricalIteration_measurable rule depth [])).sub (Lp.stronglyMeasurable endpoint).measurable
  have shifted := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal exponent) rawMeasurable.aestronglyMeasurable preserving
  simp only [Function.comp_def, electricalIteration_shift, List.append_nil] at shifted
  change eLpNorm (fun marks => W depth marks-endpoint marks) (ENNReal.ofReal exponent) μ =
    eLpNorm (fun marks => growth⁻¹^depth*electricalIteration rule marks depth address-
      endpoint (innovationTreeShift rule address marks)) (ENNReal.ofReal exponent) μ
  rw [shifted]
  apply eLpNorm_congr_ae
  filter_upwards [electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le depth] with marks equality
  rw [equality]

end
end IGSIII34.Percolation
