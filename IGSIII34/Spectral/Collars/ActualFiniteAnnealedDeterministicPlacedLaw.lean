import IGSIII34.Spectral.Collars.ActualFiniteConfigurationLawTransport
import IGSIII34.Spectral.Collars.DiscreteDeterministicPlacement
import IGSIII34.Diffusion.ActualPaperDeterministicCommonAmbient
import IGSIII34.Diffusion.ActualPaperDeterministicWalkIdentityCompletion
import IGSIII34.Diffusion.FiniteCountingOriginalCadlagIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit IGSIII34.Percolation MeasureTheory
open scoped NNReal

def actualFiniteAnnealedDeterministicClock (rule : Rule) (p growth : ℝ) (depth : ℕ) : ℝ :=
  ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth + 1)

theorem actualFiniteAnnealedDeterministicClock_positive
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    0 < actualFiniteAnnealedDeterministicClock rule p growth depth := by
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  exact pow_pos (mul_pos radiusPositive growthPositive) _

variable (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (scale : ℝ) (scalePositive : 0 < scale)
  (initial : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) scale scalePositive depth)
  {Space : Type} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
  (placement : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) scale scalePositive depth → Space)

theorem actualFiniteAnnealedDeterministicPlacedLaw_discrete (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedDeterministicClock rule p growth depth)
      (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth)
      0 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualPaperDiscreteDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      depth (diracProba (initial depth)) (placement depth) := by
  have identity := actualFiniteAnnealedPlacedPathLaw_discrete_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth) (placement depth)
  have clock := actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks scale scalePositive false depth
  simp only [Bool.false_eq_true, if_false] at clock
  simpa only [actualPaperDiscreteDeterministicPlacedCadlagLaw, actualPaperDiscreteClockCompletion,
    clock, actualFiniteAnnealedDeterministicClock, diracProba, ProbabilityMeasure.coe_mk] using identity

theorem actualFiniteAnnealedDeterministicPlacedLaw_rate_one (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedDeterministicClock rule p growth depth)
      (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth)
      1 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      false depth (diracProba (initial depth)) (placement depth) := by
  have identity := actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth)
    1 (by decide) (placement depth)
  have clock := actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks scale scalePositive false depth
  simp only [Bool.false_eq_true, if_false] at clock
  simpa only [actualPaperDeterministicPlacedCadlagLaw, actualPaperDiscreteClockCompletion,
    clock, actualFiniteAnnealedDeterministicClock, ite_true, Bool.false_eq_true, if_false] using identity

theorem actualFiniteAnnealedDeterministicPlacedLaw_inverse_degree (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedDeterministicClock rule p growth depth)
      (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth)
      2 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      true depth (diracProba (initial depth)) (placement depth) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  have identity := actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedDeterministicClock_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive depth)
    2 (by decide) (placement depth)
  have clock := actualPaperDeterministicClockRatio_normalization_completion rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks scale scalePositive true depth
  simp only [ite_true] at clock
  have ratioPositive := actualPaperDeterministicRatios_positive_of_classical_completion rule classicalRule p positive belowOne fixedPoint
    growth value growthPositive marks scale scalePositive true depth
  have countingIdentity := finiteCountingOriginalCadlagIdentity
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
    (diracProba (initial depth))
    (growth ^ (depth + 1) * (actualPaperDeterministicClockRatioCompletion rule p growth marks.val scale scalePositive true depth : ℝ))
    (mul_pos (pow_pos growthPositive _) (NNReal.coe_pos.mpr ratioPositive)) (placement depth)
  simp only [← mul_assoc, clock] at countingIdentity
  simp only [show (2 : Fin 3) ≠ 1 from by decide, if_false] at identity
  exact identity.trans (by
    simpa only [actualPaperDeterministicPlacedCadlagLaw, actualPaperDiscreteClockCompletion,
      actualFiniteAnnealedDeterministicClock, ite_true] using countingIdentity.symm)

end
end IGSIII34.Spectral
