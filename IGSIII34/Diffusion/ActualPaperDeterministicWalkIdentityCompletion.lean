import IGSIII34.Diffusion.ActualPaperDeterministicLawCompletion
import IGSIII34.Diffusion.WeightedClockRateIdentificationCompletion
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

include classicalRule growthPositive in
theorem actualPaperDeterministicClockRatio_normalization_completion (countingSpeed : Bool) (depth : ℕ) :
    (if countingSpeed then
      (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) : ℝ)
     else 2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth))) *
      growth ^ (depth+1) *
      (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ) =
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  unfold actualPaperDeterministicClockRatioCompletion
  cases countingSpeed <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [Real.coe_toNNReal _ (by positivity)]
    field_simp
  · rw [Real.coe_toNNReal _ (by positivity)]
    field_simp

local instance deterministicWalkIdentityMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance deterministicWalkIdentityBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]

def actualPaperDeterministicGlobalSampleCompletion (countingSpeed : Bool) (depth : ℕ)
    (sample : (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) × (ℕ → ℝ)) :=
  weightedHoldingGlobalSampleCompletion
    (fun vertex => if countingSpeed then finiteCountingClockDensityCompletion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
    (actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth *
      (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ))
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth) sample

include classicalRule in
theorem actualPaperDeterministicGlobalSample_original_clock_completion (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ∀ᵐ sample ∂(finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)),
      ∀ time : ℝ≥0,
        (actualPaperDeterministicGlobalSampleCompletion rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth sample).toFun time =
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth
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
    unfold actualPaperDeterministicGlobalSampleCompletion
    simp only [Bool.false_eq_true, ↓reduceIte, weightedHoldingGlobalSampleCompletion,
      weightedHoldingSampleCompletion, holdingGlobalSkorokhodSampleCompletion, one_mul]
    congr 2
    exact congrArg (fun acceleration : ℝ => acceleration * (time : ℝ))
      (actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint
        growth value growthPositive marks chemicalScale chemicalScalePositive false depth)
  · have ratioPositive := actualPaperDeterministicRatios_positive_of_classical_completion rule classicalRule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive true depth
    have identity := finiteCountingClockDensity_vertex_clock_identity_completion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) initial
      (growth ^ (depth+1) * (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive true depth : ℝ))
      (mul_pos (pow_pos growthPositive _) (NNReal.coe_pos.mpr ratioPositive))
    filter_upwards [identity] with sample equality
    intro time
    unfold actualPaperDeterministicGlobalSampleCompletion
    simp only [↓reduceIte, weightedHoldingGlobalSampleCompletion,
      holdingGlobalSkorokhodSampleCompletion]
    have normalization := actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive true depth
    simp only [↓reduceIte] at normalization
    have atTime := equality (time : ℝ) time.property
    simp only [← mul_assoc] at atTime
    rw [normalization] at atTime
    apply congrArg (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)
    simpa only [actualPaperDiscreteClockCompletion, weightedHoldingSampleCompletion, ← mul_assoc] using atTime

end
end IGSIII34.Diffusion

