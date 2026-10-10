import IGSIII.Mass.ComponentFinitePartition
import IGSIII.Mass.CylinderMassLimits

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

theorem mass_tendsto_atTop_of_positive_normalized_limit
    (mass : ℕ → ℝ) (growth limit : ℝ) (growthLarge : 1 < growth) (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => mass depth / growth ^ depth) atTop (𝓝 limit)) :
    Tendsto mass atTop atTop := by
  have lower : ∀ᶠ depth in atTop, limit / 2 * growth ^ depth ≤ mass depth := by
    have near := (tendsto_order.mp convergence).1 (limit / 2) (by linarith)
    filter_upwards [near] with depth near
    exact ((lt_div_iff₀ (pow_pos (zero_lt_one.trans growthLarge) _)).mp near).le
  exact tendsto_atTop_mono' atTop lower
    ((tendsto_pow_atTop_atTop_of_one_lt growthLarge).const_mul_atTop (by linarith : 0 < limit / 2))

/-- The actual root interior population diverges; consequently adding its
two persistent terminals cannot change any limiting probability weight. -/
theorem actual_component_root_mass_tendsto_atTop {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop := by
  obtain ⟨limit, _, _, limits⟩ := marked_oriented_vertex_limits classicalRule p positive belowOne fixedPoint
  have growthLarge : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  filter_upwards [limits] with marks limits
  exact mass_tendsto_atTop_of_positive_normalized_limit _ _ _ growthLarge
    ((limits [] .connected).2.2 rfl) (by simpa only [markedComponentVertexMass,
      componentEdgeAddress, List.map_nil, retainedComponentState, retainedComponentStateFrom] using
      (limits [] .connected).2.1)

end
end IGSIII.Chemical.Substitution
