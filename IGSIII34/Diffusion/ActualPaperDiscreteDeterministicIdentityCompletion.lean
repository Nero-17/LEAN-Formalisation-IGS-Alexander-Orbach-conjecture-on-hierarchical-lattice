import IGSIII34.Diffusion.ActualPaperDiscreteDeterministicLawCompletion
import IGSIII34.Diffusion.ActualPaperDeterministicWalkIdentityCompletion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal
variable (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
  (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
local instance paperDiscreteDeterministicVertexMeasurableCompletion (depth : ℕ) : MeasurableSpace
    (RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) := ⊤
local instance paperDiscreteDeterministicIdentityMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance paperDiscreteDeterministicIdentityBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]

/-- The law is the original jump chain at floor((rho * growth)^(depth+1) t),
not an abstract rescaling law merely carrying the same name. -/
theorem actualPaperDiscreteDeterministicGlobalLaw_original_clock_completion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualPaperDiscreteDeterministicGlobalLawCompletion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial : Measure (SkorokhodGlobalPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) =
      (finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
        (discreteGlobalSkorokhodSampleCompletion
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1))
          (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)) := by
  have normalization := actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive false depth
  simp only [Bool.false_eq_true, ↓reduceIte] at normalization
  change (finiteDiscreteWalkLaw
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
    (discreteGlobalSkorokhodSampleCompletion
      (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth+1) *
        (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive false depth : ℝ))
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)) = _
  rw [normalization]

end
end IGSIII34.Diffusion



