import IGSIII34.Spectral.Collars.CarrierProjectionMass
import IGSIII.Geometry.ActualClusterMeasuredConvergence
import IGSIII.Geometry.CriticalComponentGHP
import IGSIII34.Diffusion.ActualDegreeConvergence
import IGSIII34.Diffusion.MarkedMeasureTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Geometry
open IGSIII34.ResistanceLimit IGSIII34.Percolation IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

local instance sameCarrierGHPElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance sameCarrierGHPElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable (homeomorph : (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks.val depth [] true)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) ≃ₜ
  (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
  (inverseBirth : ∀ depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth),
    homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth vertex) =
    actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)

include inverseBirth in
theorem actual_same_carrier_counting_markedGHP
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (massGrowth : Tendsto (fun depth => markedComponentVertexMass rule marks.val depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ) (weightNonnegative : ∀ address, 0 ≤ weight address)
    (actualRatios : ∀ address, Tendsto (fun depth =>
      markedOrientedVertexMass rule marks.val depth (componentEdgeAddress address) (retainedComponentState rule marks.val address) /
        markedOrientedVertexMass rule marks.val (depth + address.length) [] .connected) atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (realizationMeasurable : Measurable realization)
    (projection : Tendsto (fun depth => levyProkhorovEDist
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0)) :
    MarkedGHPConverges
      (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (actualFiniteClusterMeasure rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive)
      (boundary.map (homeomorph.symm ∘ realization))
      (actualFiniteClusterTerminal rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive)
      (actualChemicalTerminal rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := by
  letI : CompactSpace (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks.val depth [] true)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) :=
    actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      marks.val (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  have transported := actual_inverse_carrier_boundary_projection_mass rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    homeomorph inverseBirth boundary realization realizationMeasurable projection
  have countRatios : ∀ address, Tendsto (fun depth => markedComponentVertexMass rule marks.val depth address /
      markedComponentVertexMass rule marks.val (depth + address.length) []) atTop (𝓝 (weight address)) := actualRatios
  exact actualFiniteCluster_markedGHP_of_component_radius_bounds rule classicalRule marks.val marks.property.1.1.2.1
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    massGrowth weight weightNonnegative countRatios boundary atoms (homeomorph.symm ∘ realization) transported

include inverseBirth in
theorem actual_same_carrier_degree_markedGHP
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (massGrowth : Tendsto (fun depth => markedComponentVertexMass rule marks.val depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ) (weightNonnegative : ∀ address, 0 ≤ weight address)
    (actualRatios : ∀ address, Tendsto (fun depth =>
      markedOrientedVertexMass rule marks.val depth (componentEdgeAddress address) (retainedComponentState rule marks.val address) /
        markedOrientedVertexMass rule marks.val (depth + address.length) [] .connected) atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (realizationMeasurable : Measurable realization)
    (projection : Tendsto (fun depth => levyProkhorovEDist
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0))
    (comparison : Tendsto (fun depth => levyProkhorovEDist
      (actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive depth)
      (actualFiniteClusterMeasure rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
      atTop (𝓝 0)) :
    MarkedGHPConverges
      (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive)
      (boundary.map (homeomorph.symm ∘ realization))
      (actualFiniteClusterTerminal rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive)
      (actualChemicalTerminal rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := by
  have counting := actual_same_carrier_counting_markedGHP rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    homeomorph inverseBirth eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    massGrowth weight weightNonnegative actualRatios boundary atoms realization realizationMeasurable projection
  exact markedGHPConverges_of_measure_distance_tendsto_zero _ _ _ _ _ _ counting comparison

/-- The actual degree/count comparison holds simultaneously for every
chemical metric with the actual component mesh bound, so the master
carrier and scalar need not be chosen again. -/
theorem ae_actual_degree_counting_for_any_component_mesh
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened,
      ∀ coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true),
      ∀ scale : ℝ, ∀ scalePositive : 0 < scale,
      ∀ eta coefficient : ℝ, ∀ start : ℕ, ∀ etaNonnegative : 0 ≤ eta, ∀ etaBelowOne : eta < 1,
      ∀ coefficientNonnegative : 0 ≤ coefficient,
      (∀ address opened depth, start ≤ address.length →
        (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
          coefficient * eta ^ address.length) →
      Tendsto (fun depth => levyProkhorovEDist
        (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive depth)
        (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          scale scalePositive depth)) atTop (𝓝 0) := by
  obtain ⟨jointWeight, jointLimits⟩ := actual_joint_edge_counting_word_limits classicalRule p positive belowOne fixedPoint
  filter_upwards [jointLimits, actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint]
    with marks joint massGrowth
  intro crossing coherent scale scalePositive eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  exact actual_degree_counting_tendsto_zero_of_component_radius_bounds rule marks crossing coherent scale scalePositive
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds massGrowth
    (fun address => jointWeight address marks) joint.2.2.2

end
end IGSIII34.Spectral
