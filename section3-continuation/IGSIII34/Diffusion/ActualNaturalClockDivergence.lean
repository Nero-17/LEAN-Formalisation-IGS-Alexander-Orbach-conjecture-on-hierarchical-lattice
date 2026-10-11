import IGSIII34.Diffusion.ActualNaturalClocks
import IGSIII34.Diffusion.DePoissonizationClocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

theorem accelerated_mass_tendsto_atTop_of_positive_normalized_limit
    (mass : ℕ → ℝ) (growth resistance factor limit : ℝ)
    (growthPositive : 0 < growth) (resistancePositive : 0 < resistance)
    (combinedGrowthAboveOne : 1 < growth * resistance)
    (factorPositive : 0 < factor) (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => mass depth / growth ^ depth) atTop (𝓝 limit)) :
    Tendsto (fun depth => factor * mass depth * resistance ^ depth) atTop atTop := by
  apply mass_tendsto_atTop_of_positive_normalized_limit _ (growth * resistance)
    (factor * limit) combinedGrowthAboveOne (mul_pos factorPositive limitPositive)
  convert convergence.const_mul factor using 1
  funext depth
  rw [mul_pow]
  field_simp [growthPositive.ne', resistancePositive.ne']

/-- Both exact finite-volume accelerations diverge on the original innovation
law. The lower bound on resistance growth is precisely the one furnished by
the actual electrical fixed-ray construction, rather than an assumed process limit. -/
theorem actual_natural_clocks_diverge {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (resistance : ℝ)
    (resistanceGrowthLower : deriv rule.network.reliability p ≤ resistance) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => 2 *
        ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ) * resistance ^ depth) atTop atTop ∧
      Tendsto (fun depth => (markedComponentVertexMass rule marks depth [] + 2) * resistance ^ depth)
        atTop atTop := by
  have unstable := rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale
  have resistanceAboveOne : 1 < resistance := unstable.trans_le resistanceGrowthLower
  have massGrowthAboveOne : 1 <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    unstable.trans (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
      classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have combinedGrowthAboveOne : 1 <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance := by
    nlinarith
  obtain ⟨left, coefficient, mass, leftPositive, coefficientPositive, limits⟩ :=
    actual_joint_edge_vertex_limits classicalRule p positive belowOne fixedPoint
  filter_upwards [limits] with marks properties
  constructor
  · exact accelerated_mass_tendsto_atTop_of_positive_normalized_limit _ _ resistance 2 _
      (zero_lt_one.trans massGrowthAboveOne) (zero_lt_one.trans resistanceAboveOne) combinedGrowthAboveOne
      (by norm_num) (mul_pos (zero_lt_one.trans massGrowthAboveOne) (mul_pos properties.1 leftPositive))
      properties.2.1
  · simpa only [one_mul] using accelerated_mass_tendsto_atTop_of_positive_normalized_limit _ _ resistance 1 _
      (zero_lt_one.trans massGrowthAboveOne) (zero_lt_one.trans resistanceAboveOne) combinedGrowthAboveOne
      zero_lt_one (mul_pos (zero_lt_one.trans massGrowthAboveOne) (mul_pos coefficientPositive properties.1))
      properties.2.2

end
end IGSIII34.Diffusion
