import IGSIII34.Diffusion.CountingClockResolventZeroCompletion
import IGSIII34.Diffusion.ActualCountingClockDensityCompletion
import IGSIII34.Diffusion.ActualResolventWholePointwiseCompletion

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

local instance clockCorrectorCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance clockCorrectorCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

theorem actual_clock_corrector_subsequence_zero_completion
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (countingLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalCountingMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |actualOriginalPaperClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
            chemicalScale chemicalScalePositive parameter parameterPositive
            (actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive)
            (selected index) vertex.val -
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance) : candidate = 0 := by
  let vertices := fun index => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected index)
  let edges := fun index => ClusterEdge (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
  let endpoint := fun index => clusterRetainedEndpoint (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
  let placement := fun index (vertex : vertices index) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ (selected index) vertex
  letI : ∀ index, MeasurableSpace (vertices index) := fun index => actualFiniteClusterMeasurableSpace rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected index)
  letI : ∀ index, Nonempty (vertices index) := fun index => ⟨⟨(rule.generation (selected index)).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI : ∀ index, Nonempty (edges index) := fun index => clusterEdge_nonempty (rule.generation (selected index)).network
    (stationaryConfiguration rule marks.val (selected index)) (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected index) [] true)
  let positiveDegree := fun index => cluster_degree_positive (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected index) [] true)
  have degreeWeak : Tendsto (fun index => ProbabilityMeasure.map
      (⟨degreeMeasure (endpoint index), inferInstance⟩ : ProbabilityMeasure (vertices index)) (measurable_of_finite (placement index)).aemeasurable) atTop (𝓝 measure) := by
    apply probability_weak_of_levyProkhorov_completion
    simpa only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk, actualElectricalDegreeMeasureCompletion,
      actualFiniteClusterDegreeMeasure, placement, endpoint, Function.comp_def] using degreeLimit.comp selectedAtTop
  have countingMeasureEquality (index : ℕ) :
      actualElectricalCountingMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive (selected index) =
      Measure.map (placement index) (ProbabilityTheory.uniformOn Set.univ : Measure (vertices index)) := by
    rfl
  have countingWeak : Tendsto (fun index => ProbabilityMeasure.map
      (⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩ : ProbabilityMeasure (vertices index)) (measurable_of_finite (placement index)).aemeasurable) atTop (𝓝 measure) := by
    apply probability_weak_of_levyProkhorov_completion
    simpa only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk, Function.comp_def, countingMeasureEquality] using countingLimit.comp selectedAtTop
  apply actualEnergyExtensionLinear_injective rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  rw [map_zero]
  apply countingClockResolvent_uniform_limit_zero_completion vertices edges endpoint positiveDegree parameter parameterPositive
    (fun index => growth ^ (selected index+1)) (fun index => (pow_pos growthPositive _).le) measure placement degreeWeak countingWeak
  intro tolerance tolerancePositive
  filter_upwards [uniform tolerance tolerancePositive] with index close
  intro vertex
  letI : Nonempty (vertices index) := ⟨⟨(rule.generation (selected index)).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected index) [] true)
  have restricted := retainedPotentialExtension_retained_completion
    (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index))
    (actualPaperClockGraphResolventCompletion rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive (selected index) growth growthPositive parameter parameterPositive
      (actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected index))) vertex
  have equality : actualOriginalPaperClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive parameter parameterPositive
      (actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive) (selected index) vertex.val =
      finiteGraphResolvent (Vertex := vertices index) (endpoint index) (positiveDegree index) parameter (2 * Fintype.card (edges index) * growth ^ (selected index+1)) parameterPositive (by positivity)
        (fun vertex => finiteCountingClockDensityCompletion (endpoint index) vertex - 1) vertex := restricted
  rw [← equality]
  exact close vertex

end
end IGSIII34.Diffusion

