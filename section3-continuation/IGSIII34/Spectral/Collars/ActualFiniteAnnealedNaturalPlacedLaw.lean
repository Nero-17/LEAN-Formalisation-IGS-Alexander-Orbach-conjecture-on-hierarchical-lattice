import IGSIII34.Spectral.Collars.ActualFiniteConfigurationLawTransport
import IGSIII34.Spectral.Collars.ActualFiniteAnnealedNaturalClockIdentity
import IGSIII34.ResistanceLimit.ActualCommonChemicalPaperLaw
import IGSIII34.ResistanceLimit.ActualCommonChemicalContinuousPaperLaw
import IGSIII34.Diffusion.ActualCommonVertexSpeedChemicalCadlagCompletion20261011
import IGSIII34.Diffusion.FiniteCountingOriginalCadlagIdentity
import IGSIII34.Diffusion.FiniteUnitWeightCadlagIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit IGSIII34.Percolation MeasureTheory
open scoped NNReal
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (scale : ℝ) (scalePositive : 0 < scale)
  (initial : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) scale scalePositive depth)
  {Space : Type} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
  (placement : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) scale scalePositive depth → Space)

 theorem actualFiniteAnnealedNaturalPlacedLaw_discrete (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedNaturalClock rule scale scalePositive depth growth 0 (stationaryConfiguration rule marks.val depth))
      (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
        (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 0)
      0 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualPaperPlacedDiscreteCadlagLaw rule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      (fun depth => diracProba (initial depth)) placement depth := by
  have identity := actualFiniteAnnealedPlacedPathLaw_discrete_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 0) (placement depth)
  have clock := actualFiniteAnnealedNaturalClock_original_identity rule (stationaryConfiguration rule marks.val) scale scalePositive depth
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive (0 : Fin 3)
  simp only [show (0 : Fin 3) ≠ 2 from by decide, if_false] at clock
  simpa only [clock, actualPaperPlacedDiscreteCadlagLaw, actualPaperDiscreteClockCompletion20261011, diracProba] using identity

 theorem actualFiniteAnnealedNaturalPlacedLaw_rate_one (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedNaturalClock rule scale scalePositive depth growth 1 (stationaryConfiguration rule marks.val depth))
      (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
        (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 1)
      1 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualPaperPlacedContinuousCadlagLaw rule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      (fun depth => diracProba (initial depth)) placement depth := by
  have identity := actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 1)
    1 (by decide) (placement depth)
  have clock := actualFiniteAnnealedNaturalClock_original_identity rule (stationaryConfiguration rule marks.val) scale scalePositive depth
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive (1 : Fin 3)
  simp only [show (1 : Fin 3) ≠ 2 from by decide, if_false] at clock
  simp only [ite_true, finiteUnitWeightCadlagIdentity] at identity
  simpa only [clock, actualPaperPlacedContinuousCadlagLaw, actualPaperDiscreteClockCompletion20261011] using identity

 theorem actualFiniteAnnealedNaturalPlacedLaw_inverse_degree (depth : ℕ) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) (initial depth).val
      (actualFiniteAnnealedNaturalClock rule scale scalePositive depth growth 2 (stationaryConfiguration rule marks.val depth))
      (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
        (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 2)
      2 (placement depth ∘ actualAnnealedFiniteVertexEquiv rule (stationaryConfiguration rule marks.val) scale scalePositive depth) =
    actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks scale scalePositive
      depth (diracProba (initial depth)) (placement depth) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  have identity := actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport rule (stationaryConfiguration rule marks.val)
    scale scalePositive depth (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    (initial depth) _ (actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks.val) scale scalePositive depth
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive 2)
    2 (by decide) (placement depth)
  have clock := actualFiniteAnnealedNaturalClock_original_identity rule (stationaryConfiguration rule marks.val) scale scalePositive depth
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true) growth growthPositive (2 : Fin 3)
  simp only [ite_true, Nat.card_eq_fintype_card] at clock
  simp only [show (2 : Fin 3) ≠ 1 from by decide, if_false] at identity
  simp only [clock] at identity
  rw [← finiteCountingOriginalCadlagIdentity _ _ _ (growth ^ (depth + 1)) (pow_pos growthPositive _) (placement depth)] at identity
  exact identity

end
end IGSIII34.Spectral
