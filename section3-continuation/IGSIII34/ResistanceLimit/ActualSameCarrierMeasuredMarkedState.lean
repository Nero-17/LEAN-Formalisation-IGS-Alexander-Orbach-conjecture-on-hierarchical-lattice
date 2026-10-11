import IGSIII34.ResistanceLimit.ActualCommonChemicalMeasuredMarkedState
import IGSIII34.Diffusion.ActualDegreeMeasure

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Chemical.SmallBall IGSIII34.Spectral IGSIII34.Percolation IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology

/-- The two original finite probability masses; true is counting, false is degree. -/
def actualBothFiniteClusterProbability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) (counting : Bool) :
    ProbabilityMeasure (ActualFiniteCluster rule configuration scale scalePositive depth) :=
  if counting then ⟨actualFiniteClusterMeasure rule configuration scale scalePositive depth, inferInstance⟩ else
    ⟨actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth, inferInstance⟩

@[simp] theorem actualBothFiniteClusterProbability_counting (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    (actualBothFiniteClusterProbability rule configuration crossing scale scalePositive depth true : Measure _) =
      actualFiniteClusterMeasure rule configuration scale scalePositive depth := rfl

@[simp] theorem actualBothFiniteClusterProbability_degree (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    (actualBothFiniteClusterProbability rule configuration crossing scale scalePositive depth false : Measure _) =
      actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth := rfl

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

local instance sameMarkedElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance sameMarkedElectricalBorel : BorelSpace
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
/-- On the SAME actual harmonic carrier and prescribed common ambient,
the full compact images, both original terminals and BOTH ORIGINAL masses
converge. Mass convergence is derived from the actual born-projection LP
inputs, not assumed for the ambient placements. -/
theorem actual_same_carrier_measured_marked_state
    {Ambient : Type*} [MetricSpace Ambient] [TopologicalSpace.SeparableSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (realizationMeasurable : Measurable realization)
    (bornProjectionLP : ∀ counting, Tendsto (fun depth => levyProkhorovEDist
      ((actualBothFiniteClusterProbability rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive depth counting : Measure _).map
        (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val, marks.property.1.1⟩ depth vertex))
      (boundary.map realization)) atTop (𝓝 0))
    (target : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient)
    (targetIsometry : Isometry target)
    (sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient)
    (sourceIsometry : ∀ depth, Isometry (sources depth))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)) < tolerance)
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) /
        chemicalScale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length) :
    letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      marks.val (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    Tendsto (fun depth => continuousNonemptyCompactRange (sources depth) (sourceIsometry depth).continuous)
      atTop (𝓝 (continuousNonemptyCompactRange target targetIsometry.continuous)) ∧
    (∀ side, Tendsto (fun depth => sources depth (actualFiniteClusterTerminal rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive depth side)) atTop
      (𝓝 (target (actualChemicalTerminal rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence side)))) ∧
    ∀ counting,
      Tendsto (fun depth => (actualBothFiniteClusterProbability rule (stationaryConfiguration rule marks.val)
          (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
          chemicalScale chemicalScalePositive depth counting).map (measurable_of_finite (sources depth)).aemeasurable) atTop
        (𝓝 (ProbabilityMeasure.map (⟨boundary.map realization, Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable⟩ :
          ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
          (targetIsometry.continuous.comp homeomorph.symm.continuous).measurable.aemeasurable)) ∧
      Tendsto (fun depth => levyProkhorovEDist
        ((actualBothFiniteClusterProbability rule (stationaryConfiguration rule marks.val)
          (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
          chemicalScale chemicalScalePositive depth counting : Measure _).map (sources depth))
        ((boundary.map realization).map (target ∘ homeomorph.symm))) atTop (𝓝 0) := by
  letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    marks.val (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  refine ⟨actual_common_chemical_compact_images_tendsto rule classicalRule marks.val
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    target targetIsometry sources sourceIsometry placementClose
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds, ?_, ?_⟩
  · intro side
    exact actual_common_chemical_terminal_tendsto rule classicalRule marks.val marks.property.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence target sources placementClose side
  · intro counting
    exact actual_same_carrier_placed_mass rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence homeomorph inverseBirth
      boundary realization realizationMeasurable
      (fun depth => actualBothFiniteClusterProbability rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive depth counting)
      (bornProjectionLP counting) target targetIsometry.continuous sources placementClose

end
end IGSIII34.ResistanceLimit


