import IGSIII34.Diffusion.ElectricalCountingConvergenceCompletion20261011
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion20261011

/-! Degree measures converge to any actual boundary realization using the
same vertex-ratio weights. This universal statement permits the diffusion
and spectral constructions to retain one mass measure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem ae_actual_natural_counting_mass_tendsto_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryElectricalTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) marks,
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word) marks)),
      ∀ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
          ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩,
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          marks typical depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0) →
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      Tendsto (fun depth => levyProkhorovEDist
        (actualElectricalCountingMeasureCompletion20261011 rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive depth) (boundary.map realization)) atTop (𝓝 0) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  obtain ⟨eta, inverseBelowEta, etaBelowOne⟩ := exists_between (inv_lt_one_of_one_lt₀ natural.aboveOne)
  have etaPositive := (inv_pos.mpr growthPositive).trans inverseBelowEta
  have productGreaterThanOne : 1 < natural.growth * eta := by
    have multiplied := mul_lt_mul_of_pos_left inverseBelowEta growthPositive
    simpa only [mul_inv_cancel₀ growthPositive.ne'] using multiplied
  filter_upwards [actualRatios, nonnegative,
    actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive growthPositive growthBounds (natural.amplitude • natural.field) endpointFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks ratios positiveWeights massGrowth fields mesh
  obtain ⟨start, radiusBounds⟩ := mesh
  intro typical boundary probability atoms realization projection chemicalScale chemicalScalePositive
  letI := probability
  have vertexRatios : ∀ address, Tendsto (fun depth => markedComponentVertexMass rule marks depth address /
      markedComponentVertexMass rule marks (depth + address.length) []) atTop (𝓝 (weight address marks)) := ratios
  exact actualElectrical_counting_mass_tendsto_completion20261011 rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks, typical⟩ fields
    eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le) radiusBounds
    chemicalScale chemicalScalePositive massGrowth (fun address => weight address marks) positiveWeights vertexRatios
    boundary atoms realization projection

end
end IGSIII34.Diffusion