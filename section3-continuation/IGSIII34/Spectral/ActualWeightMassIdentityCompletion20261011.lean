import IGSIII34.Spectral.GroupedSocketMassCompletion20261011
import IGSIII.Mass.ComponentCylinderWeights

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology

theorem actual_mass_continuation_connected_positive_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < continuation.mass .connected marks := by
  obtain ⟨limit, _, _, convergence, _, _⟩ :=
    exists_actual_mass_field_all_nat_moments classicalRule p positive belowOne fixedPoint
  filter_upwards [continuation.actualLimits, convergence] with marks actual convergence
  have root := actual [] .connected
  change Tendsto (fun depth => markedOrientedVertexMass rule marks depth [] .connected /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth)
    atTop (𝓝 (continuation.mass .connected marks)) at root
  have same := tendsto_nhds_unique root (convergence [] .connected).2.1
  rw [same]
  exact (convergence [] .connected).2.2 rfl

/-- The original Section 2 vertex-ratio weights equal the actual continuation
mass divided by the Perron scale and the same root mass. This applies to any
version of those actual ratios, including the typical-mass construction. -/
theorem actual_vertex_ratio_weight_mass_identity_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < continuation.mass .connected marks ∧ ∀ address,
        continuation.mass .connected marks * weight address marks =
          continuation.mass (retainedComponentState rule marks address)
            (innovationTreeShift rule (componentEdgeAddress address) marks) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^address.length := by
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [actualRatios, continuation.actualLimits,
    actual_mass_continuation_connected_positive_completion20261011 rule classicalRule p positive belowOne fixedPoint continuation]
    with marks ratios limits rootPositive
  refine ⟨rootPositive, ?_⟩
  intro address
  have root := limits [] .connected
  change Tendsto (fun depth => markedOrientedVertexMass rule marks depth [] .connected /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth)
    atTop (𝓝 (continuation.mass .connected marks)) at root
  have denominator := (root.comp (tendsto_add_atTop_nat address.length)).mul_const
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^address.length)
  have ratio := (limits (componentEdgeAddress address) (retainedComponentState rule marks address)).div
    denominator (mul_pos rootPositive (pow_pos radiusPositive address.length)).ne'
  have actualRatio : Tendsto (fun depth =>
      markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
      atTop (𝓝 (continuation.mass (retainedComponentState rule marks address)
        (innovationTreeShift rule (componentEdgeAddress address) marks) /
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^address.length *
            continuation.mass .connected marks))) := by
    convert ratio using 1
    · funext depth
      simp only [Function.comp_apply, Pi.div_apply]
      rw [pow_add]
      field_simp
    · congr 1
      ring
  rw [tendsto_nhds_unique (ratios address) actualRatio]
  field_simp

end
end IGSIII34.Spectral
