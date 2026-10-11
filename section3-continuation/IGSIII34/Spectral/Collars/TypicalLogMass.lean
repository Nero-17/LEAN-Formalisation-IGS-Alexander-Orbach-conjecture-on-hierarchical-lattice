import IGSIII34.Spectral.Collars.MassLogarithm
import IGSIII34.Spectral.ActualBoundaryTypicalMassCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

/-- The logarithmic mass conclusion holds for every version of the actual
vertex-ratio weights and every boundary law with those original atoms.
Thus it applies to the same law used for the physical realization. -/
theorem actual_boundary_vertex_ratio_typical_log_mass
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      (∀ depth word, boundary {path | path depth = word} =
        ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary,
        (∀ depth, 0 < weight (List.ofFn (path depth)) marks) ∧
        Tendsto (fun depth : ℕ => Real.log (weight (List.ofFn (path depth)) marks) / depth)
          atTop (𝓝 (-Real.log
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) := by
  obtain ⟨canonicalWeight, canonicalProperties⟩ := exists_actual_component_weight_subexponential_upper
    classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [canonicalProperties, actualRatios,
    actual_boundary_vertex_ratio_typical_lower_completion20261011 rule classicalRule p positive belowOne
      fixedPoint weight actualRatios] with marks canonical actual lower
  have same (address : List (Fin rule.edges × Bool)) : weight address marks = canonicalWeight address marks :=
    tendsto_nhds_unique (actual address) (canonical.2.1 address).2.2.1
  intro boundary atoms
  filter_upwards [lower boundary atoms] with path estimates
  refine ⟨estimates.1, ?_⟩
  apply logarithmic_mass_limit_of_subexponential_bounds
    (fun depth => weight (List.ofFn (path depth)) marks) _ radiusPositive estimates.1
  intro growth greater
  obtain ⟨coefficient, coefficientPositive, upperThreshold, upper⟩ := canonical.2.2 growth greater
  obtain ⟨lowerThreshold, lower⟩ := eventually_atTop.mp (estimates.2 growth greater)
  refine ⟨coefficient, coefficientPositive, max lowerThreshold upperThreshold, ?_⟩
  intro depth after
  refine ⟨lower depth ((le_max_left _ _).trans after), ?_⟩
  rw [same]
  simpa only [List.length_ofFn] using upper (List.ofFn (path depth))
    (by simpa only [List.length_ofFn] using ((le_max_right lowerThreshold upperThreshold).trans after))

end
end IGSIII34.Spectral
