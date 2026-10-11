import IGSIII34.Diffusion.ActualPaperDeterministicWalkIdentityCompletion20261011
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
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
local instance deterministicLawIdentityMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance deterministicLawIdentityBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]

def actualPaperDeterministicOriginalSampleCompletion20261011 (countingSpeed : Bool) (depth : ℕ)
    (sample : (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) × (ℕ → ℝ)) :
    SkorokhodGlobalPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) :=
  ⟨fun time => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth
    (holdingTimePath sample.1
      (fun index => if countingSpeed then sample.2 index / degree
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) (sample.1 index) else sample.2 index)
      ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1)) * time))⟩

/-- The law in the deterministic-clock corollary is precisely the original
finite walk, with holding times Exp(1) or Exp(1)/degree and the deterministic
acceleration (rho * growth)^(depth+1). -/
theorem actualPaperDeterministicGlobalLaw_original_clock_completion20261011 (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualPaperDeterministicGlobalLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth initial : Measure _) =
      (finiteContinuousWalkSampleLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
        (actualPaperDeterministicOriginalSampleCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth) := by
  change (finiteContinuousWalkSampleLaw
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
    (actualPaperDeterministicGlobalSampleCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth) = _
  apply Measure.map_congr
  filter_upwards [actualPaperDeterministicGlobalSample_original_clock_completion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth initial] with sample equality
  exact congrArg SkorokhodGlobalPathCompletion20261011.mk (funext equality)

end
end IGSIII34.Diffusion

