import IGSIII34.Percolation.ElectricalRealMoments
import IGSIII34.Probability.AllOrderConvergence
import IGSIII34.Percolation.ElectricalAmplitudes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

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
theorem electricalOrbit_absolute_error_moment_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Tendsto (fun depth => ∫ marks, |W depth marks-endpoint marks|^exponent ∂μ) atTop (𝓝 0) := by
  exact absolute_error_moment_tendsto_of_ae_and_uniform_real_moments μ (fun depth marks => W depth marks)
    (fun depth => (Lp.stronglyMeasurable _).measurable)
    (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds)
    (electricalOrbit_uniform_integrable_real_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds)
    endpoint (Lp.stronglyMeasurable _).measurable
    (electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
      (fun depth => (growthBounds depth).1) endpoint membership)
    (electricalOmega_integrable_real_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint membership)
    (electricalOrbitLp_tendsto_ae_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership) exponent exponentPositive

theorem innovationTreeShift_integral (address : List (Fin rule.edges))
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) (measurable : Measurable value) :
    (∫ marks, value (innovationTreeShift rule address marks) ∂μ) = ∫ marks, value marks ∂μ := by
  have equality : (∫ marks, value marks ∂μ.map (innovationTreeShift rule address)) =
      ∫ marks, value (innovationTreeShift rule address marks) ∂μ :=
    integral_map_of_stronglyMeasurable (innovationTreeShift_measurable rule address) measurable.stronglyMeasurable
  rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at equality
  exact equality.symm

include classical constantPositive growthPositive growthBounds in
theorem electricalIteration_real_moment_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (address : List (Fin rule.edges)) (exponent : ℝ) :
    Tendsto (fun depth => ∫ marks, (growth⁻¹^depth*electricalIteration rule marks depth address)^exponent ∂μ) atTop
      (𝓝 (∫ marks, (electricalField rule p positive belowOne fixedPoint endpoint address marks)^exponent ∂μ)) := by
  have endpointIntegral := innovationTreeShift_integral rule p positive belowOne fixedPoint address
    (fun marks => (endpoint marks)^exponent) ((Lp.stronglyMeasurable endpoint).measurable.pow measurable_const)
  change (∫ marks, (electricalField rule p positive belowOne fixedPoint endpoint address marks)^exponent ∂μ) = _ at endpointIntegral
  rw [endpointIntegral]
  apply (electricalOrbit_real_moment_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    constantPositive growthPositive growthBounds endpoint endpointFixed membership exponent).congr'
  apply Eventually.of_forall
  intro depth
  have shifted := innovationTreeShift_integral rule p positive belowOne fixedPoint address
    (fun marks => (growth⁻¹^depth*electricalIteration rule marks depth [])^exponent)
    ((measurable_const.mul (electricalIteration_measurable rule depth [])).pow measurable_const)
  simp only [electricalIteration_shift, List.append_nil] at shifted
  change (∫ marks, (W depth marks)^exponent ∂μ) =
    ∫ marks, (growth⁻¹^depth*electricalIteration rule marks depth address)^exponent ∂μ
  rw [shifted]
  exact integral_congr_ae ((electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le depth).mono
    (fun marks equality => by rw [equality]))

include classical constantPositive growthPositive growthBounds in
theorem electricalIteration_absolute_error_moment_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (address : List (Fin rule.edges)) (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Tendsto (fun depth => ∫ marks,
      |growth⁻¹^depth*electricalIteration rule marks depth address-
        electricalField rule p positive belowOne fixedPoint endpoint address marks|^exponent ∂μ) atTop (𝓝 0) := by
  apply (electricalOrbit_absolute_error_moment_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    constantPositive growthPositive growthBounds endpoint endpointFixed membership exponent exponentPositive).congr'
  apply Eventually.of_forall
  intro depth
  have shifted := innovationTreeShift_integral rule p positive belowOne fixedPoint address
    (fun marks => |growth⁻¹^depth*electricalIteration rule marks depth []-endpoint marks|^exponent)
    ((continuous_abs.measurable.comp ((measurable_const.mul (electricalIteration_measurable rule depth [])).sub
      (Lp.stronglyMeasurable endpoint).measurable)).pow measurable_const)
  simp only [electricalIteration_shift, List.append_nil] at shifted
  change (∫ marks, |growth⁻¹^depth*electricalIteration rule marks depth address-
    electricalField rule p positive belowOne fixedPoint endpoint address marks|^exponent ∂μ) = _ at shifted
  change (∫ marks, |W depth marks-endpoint marks|^exponent ∂μ) =
    ∫ marks, |growth⁻¹^depth*electricalIteration rule marks depth address-
      electricalField rule p positive belowOne fixedPoint endpoint address marks|^exponent ∂μ
  rw [shifted]
  exact integral_congr_ae ((electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le depth).mono
    (fun marks equality => by rw [equality]))

end
end IGSIII34.Percolation

