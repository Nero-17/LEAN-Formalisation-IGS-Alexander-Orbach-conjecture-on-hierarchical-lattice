import IGSIII34.Spectral.Collars.DiscreteDeterministicPlacement
import IGSIII34.Diffusion.ActualPaperDiscreteDeterministicIdentityCompletion20261011
import IGSIII34.Spectral.Collars.DiscreteSameObservedLimit
import IGSIII34.Diffusion.ActualPaperDiscreteDeterministicLawCompletion20261011
import IGSIII34.Diffusion.DiscreteCadlagWeakCompletion20261011
import IGSIII34.Diffusion.ActualPaperDeterministicLawIdentityCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedCommonEmbeddingCompletion20261011
import IGSIII34.Diffusion.UsualLocalJ1PathLaw
import IGSIII34.Diffusion.UsualLocalJ1SpatialWeakTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
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

/-- Exact original jump-chain law at the physical deterministic acceleration,
with the already prescribed finite placements. -/
theorem actualPaperDiscreteDeterministicPlacedCadlagLaw_original_clock (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient) :
    (((actualPaperDiscreteDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive depth initial placement).map measurable_subtype_coe.aemeasurable) :
        Measure (SkorokhodGlobalPathCompletion20261011 Ambient)) =
      (finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
        (discreteGlobalSkorokhodSampleCompletion20261011
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1)) placement) := by
  have normalization := actualPaperDeterministicClockRatio_normalization_completion20261011 rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks chemicalScale chemicalScalePositive false depth
  simp only [Bool.false_eq_true, ↓reduceIte] at normalization
  simp only [actualPaperDiscreteDeterministicPlacedCadlagLaw, discreteCadlagProbability_val_completion20261011]
  change (finiteDiscreteWalkLaw
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial : Measure _)).map
    (discreteGlobalSkorokhodSampleCompletion20261011
      (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth+1) *
        (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive false depth : ℝ)) placement) = _
  rw [normalization]

end
end IGSIII34.Diffusion
