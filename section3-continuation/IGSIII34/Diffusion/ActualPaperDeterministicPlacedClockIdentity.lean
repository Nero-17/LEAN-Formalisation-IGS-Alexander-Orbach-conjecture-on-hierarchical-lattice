import IGSIII34.Diffusion.ActualPaperDeterministicCommonAmbient
import IGSIII34.Diffusion.WeightedClockRateIdentificationCompletion20261011
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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

variable {Ambient : Type*} [MetricSpace Ambient] [CompactSpace Ambient]
  [MeasurableSpace Ambient] [BorelSpace Ambient]
def actualPaperDeterministicPlacedGlobalSample (countingSpeed : Bool) (depth : ℕ)
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient)
    (sample : (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) × (ℕ → ℝ)) :=
  weightedHoldingGlobalSampleCompletion20261011
    (fun vertex => if countingSpeed then finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth *
      (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ))
    placement sample

include classicalRule growthPositive in
theorem actualPaperDeterministicPlacedGlobalSample_original_clock (countingSpeed : Bool) (depth : ℕ)
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ∀ᵐ sample ∂(finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)),
      ∀ time : ℝ≥0,
        (actualPaperDeterministicPlacedGlobalSample rule p positive belowOne fixedPoint growth value marks chemicalScale chemicalScalePositive countingSpeed depth placement sample).toFun time =
          placement
            (holdingTimePath sample.1
              (fun index => if countingSpeed then sample.2 index / degree
                (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) (sample.1 index) else sample.2 index)
              ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1)) * time)) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  cases countingSpeed
  · filter_upwards [] with sample
    intro time
    unfold actualPaperDeterministicPlacedGlobalSample
    simp only [Bool.false_eq_true, ↓reduceIte, weightedHoldingGlobalSampleCompletion20261011,
      weightedHoldingSampleCompletion20261011, holdingGlobalSkorokhodSampleCompletion20261011, one_mul]
    congr 2
    exact congrArg (fun acceleration : ℝ => acceleration * (time : ℝ))
      (actualPaperDeterministicClockRatio_normalization_completion20261011 rule classicalRule p positive belowOne fixedPoint
        growth value growthPositive marks chemicalScale chemicalScalePositive false depth)
  · have ratioPositive := actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive true depth
    have identity := finiteCountingClockDensity_vertex_clock_identity_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) initial
      (growth ^ (depth+1) * (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive true depth : ℝ))
      (mul_pos (pow_pos growthPositive _) (NNReal.coe_pos.mpr ratioPositive))
    filter_upwards [identity] with sample equality
    intro time
    unfold actualPaperDeterministicPlacedGlobalSample
    simp only [↓reduceIte, weightedHoldingGlobalSampleCompletion20261011,
      holdingGlobalSkorokhodSampleCompletion20261011]
    have normalization := actualPaperDeterministicClockRatio_normalization_completion20261011 rule classicalRule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive true depth
    simp only [↓reduceIte] at normalization
    have atTime := equality (time : ℝ) time.property
    simp only [← mul_assoc] at atTime
    rw [normalization] at atTime
    apply congrArg placement
    simpa only [actualPaperDiscreteClockCompletion20261011, weightedHoldingSampleCompletion20261011, ← mul_assoc] using atTime


def actualPaperDeterministicPlacedOriginalSample (countingSpeed : Bool) (depth : ℕ)
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient)
    (sample : (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) × (ℕ → ℝ)) :
    SkorokhodGlobalPathCompletion20261011 Ambient :=
  ⟨fun time => placement (holdingTimePath sample.1
    (fun index => if countingSpeed then sample.2 index / degree
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) (sample.1 index) else sample.2 index)
    ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1)) * time))⟩

/-- Exact identification in the prescribed common ambient with the original
Exp(1), respectively Exp(1)/degree, waiting-time walk at acceleration
(rho * growth)^(depth+1). -/
theorem actualPaperDeterministicPlacedCadlagLaw_original_clock (countingSpeed : Bool) (depth : ℕ)
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ((actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive countingSpeed depth initial placement).map measurable_subtype_coe.aemeasurable : Measure _) =
    (finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
      (actualPaperDeterministicPlacedOriginalSample rule p positive belowOne fixedPoint growth value marks chemicalScale chemicalScalePositive
        countingSpeed depth placement) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  unfold actualPaperDeterministicPlacedCadlagLaw
  rw [finiteWeightedCadlagProbability_val_completion20261011]
  change (finiteContinuousWalkSampleLaw
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
    (actualPaperDeterministicPlacedGlobalSample rule p positive belowOne fixedPoint growth value marks chemicalScale chemicalScalePositive
      countingSpeed depth placement) = _
  apply Measure.map_congr
  filter_upwards [actualPaperDeterministicPlacedGlobalSample_original_clock rule classicalRule p positive belowOne fixedPoint growth value
    growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth placement initial] with sample equality
  exact congrArg SkorokhodGlobalPathCompletion20261011.mk (funext equality)

end
end IGSIII34.Diffusion
