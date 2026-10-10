import IGSIII34.Probability.UniformRealMoments
import IGSIII34.Percolation.ElectricalFutureMean
import IGSIII34.Percolation.ElectricalAlmostSure
import IGSIII34.Probability.RealMomentConvergence

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
theorem electricalOrbit_uniform_integrable_positive_natural_moment (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (W depth marks)^power) μ ∧
        (∫ marks, (W depth marks)^power ∂μ) ≤ bound := by
  obtain ⟨bound, finite, bounds⟩ := electricalOrbitLp_uniform_positive_moment rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive (fun depth => (growthBounds depth).2) power
  exact ⟨bound.toReal, fun depth => positive_natural_moment_of_lintegral_bound μ (W depth)
    (Lp.stronglyMeasurable _).measurable
    (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds depth)
    power bound finite (bounds depth)⟩

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_uniform_integrable_real_moment (exponent : ℝ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (W depth marks)^exponent) μ ∧
        (∫ marks, (W depth marks)^exponent ∂μ) ≤ bound := by
  exact uniform_real_moments_of_uniform_natural_moments μ (fun depth marks => W depth marks)
    (fun depth => (Lp.stronglyMeasurable _).measurable)
    (electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds)
    (electricalOrbit_uniform_integrable_positive_natural_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds)
    (electricalOrbit_uniform_integrable_inverse_natural_moment rule classical p positive belowOne fixedPoint
      growth growthPositive (fun depth => (growthBounds depth).1)) exponent

include classical constantPositive growthPositive growthBounds in
theorem electricalOmega_integrable_real_moment
    (endpoint : Lp ℝ 2 μ) (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (exponent : ℝ) : Integrable (fun marks => (endpoint marks)^exponent) μ := by
  apply integrable_real_power_of_all_natural_moments μ endpoint (Lp.stronglyMeasurable _).measurable
    (electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
      (fun depth => (growthBounds depth).1) endpoint membership)
  · intro power
    obtain ⟨bound, finite, bounds⟩ := electricalOmega_uniform_positive_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive (fun depth => (growthBounds depth).2) power
    exact ne_top_of_le_ne_top finite (bounds endpoint membership)
  · intro power
    obtain ⟨bound, finite, bounds⟩ := electricalOmega_uniform_inverse_moment rule classical p positive belowOne fixedPoint
      growth growthPositive (fun depth => (growthBounds depth).1) power
    exact ne_top_of_le_ne_top finite (bounds endpoint membership)

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_real_moment_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) (exponent : ℝ) :
    Tendsto (fun depth => ∫ marks, (W depth marks)^exponent ∂μ) atTop
      (𝓝 (∫ marks, (endpoint marks)^exponent ∂μ)) := by
  exact real_moment_tendsto_of_ae_and_uniform_real_moments μ (fun depth marks => W depth marks)
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
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership) exponent

end
end IGSIII34.Percolation


