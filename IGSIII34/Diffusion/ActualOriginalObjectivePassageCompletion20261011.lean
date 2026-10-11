import IGSIII34.Diffusion.OriginalObjectiveMinimumCompletion20261011
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance originalObjectiveCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance originalObjectiveCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

/-- The complete original objective converges along every actual uniform
potential subsequence, using the canonical degree speed measure. -/
theorem actualOriginalDegreeObjective_tendsto_completion20261011
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (target forcing : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |potentials (selected index) vertex.val - target
          (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance)
    (parameter limitEnergy : ℝ)
    (energyLimit : Tendsto (fun index => sourceComponentEnergy
      (network (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)))
      (fun _ => (growth ^ (selected index + 1))⁻¹) (potentials (selected index))) atTop (𝓝 limitEnergy)) :
    Tendsto (fun index => actualOriginalDegreeObjectiveCompletion20261011 rule p positive belowOne fixedPoint growth value marks
      chemicalScale chemicalScalePositive (selected index) parameter
      (fun vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)) (potentials (selected index))) atTop
      (𝓝 (parameter * (∫ point, target point ^ 2 ∂measure) + limitEnergy -
        2 * (∫ point, forcing point * target point ∂measure))) := by
  let vertices := fun index => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected index)
  let endpoint := fun index => clusterRetainedEndpoint
    (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
  let placement := fun index (vertex : vertices index) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ (selected index) vertex
  let measures : ∀ index, ProbabilityMeasure (vertices index) := fun index =>
    ⟨actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive (selected index), by
      letI := clusterEdge_nonempty (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
        (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected index) [] true)
      infer_instance⟩
  have weak : Tendsto (fun index => (measures index).map (measurable_of_finite (placement index)).aemeasurable) atTop (𝓝 measure) := by
    apply probability_weak_of_levyProkhorov_completion20261011
    simpa only [measures, placement, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk,
      actualElectricalDegreeMeasureCompletion20261011, Function.comp_def] using degreeLimit.comp selectedAtTop
  have integrals := uniform_finite_quadratic_integrals_completion20261011 vertices measures measure placement weak
    (fun index vertex => potentials (selected index) vertex.val) target forcing uniform
  have convergence := ((integrals.1.const_mul parameter).add energyLimit).sub (integrals.2.const_mul 2)
  simpa only [actualOriginalDegreeObjectiveCompletion20261011, measures, placement, ProbabilityMeasure.coe_mk] using convergence

end
end IGSIII34.Diffusion





