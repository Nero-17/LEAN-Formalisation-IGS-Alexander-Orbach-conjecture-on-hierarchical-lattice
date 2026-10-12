import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointKernel
import IGSIII34.Spectral.Collars.ActualFiniteConfigurationStateTransport
import IGSIII34.Spectral.Collars.ActualFiniteConfigurationLawTransport
import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicSelectedStart
import IGSIII34.Diffusion.OriginalJointCompactPathLawIsometry
import IGSIII34.Diffusion.WholeCadlagProbabilityTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory TopologicalSpace

theorem actualFullConfigurationState_eq_fullState
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) :
    actualFullConfigurationState rule configuration scale scalePositive depth crossing =
      originalJointCompactFullState
        (actualFullConfigurationMark rule configuration scale scalePositive depth crossing)
        (actualFullConfigurationMass rule configuration scale scalePositive depth crossing) := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    exact Set.range_id
  · rfl

/-- This probability is carried by the original full-configuration finite
chemical metric carrier. Its equality with the literal original discrete
or weighted walk law follows from the configuration transport theorems. -/
def actualFullConfigurationPathLaw
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion
      (ActualFiniteCluster rule configuration scale scalePositive depth)) :=
  (actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth
    (configuration depth) crossing initial clock clockPositive kind).map
    (skorokhodCadlagContinuousCarrierMap_continuous_completion
      (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
      (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous).measurable.aemeasurable

theorem actualFullConfigurationPathLaw_placed
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3)
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Ambient)
    (continuous : Continuous placement) :
    (actualFullConfigurationPathLaw rule configuration scale scalePositive depth crossing initial
      clock clockPositive kind).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion
        placement continuous).measurable.aemeasurable =
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (configuration depth)
      crossing initial clock clockPositive kind
      (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) := by
  unfold actualFullConfigurationPathLaw
  rw [skorokhodCadlagProbabilityMap_comp]
  exact (actualFiniteAnnealedPlacedPathLaw_eq_canonical_map rule scale scalePositive depth
    (configuration depth) crossing initial clock clockPositive kind _
    (continuous.comp (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous)).symm

theorem actualFiniteOriginalJointResponse_configuration_transport
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : Configuration (rule.generation depth).edges → ℝ)
    (clockPositive : 0 < clock (configuration depth)) (kind : Fin 3) :
    actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind
      (configuration depth, initial) =
    originalJointCompactPathLaw
      (actualFullConfigurationMark rule configuration scale scalePositive depth crossing)
      (actualFullConfigurationMass rule configuration scale scalePositive depth crossing)
      (actualFullConfigurationPathLaw rule configuration scale scalePositive depth crossing initial
        (clock (configuration depth)) clockPositive kind) := by
  rw [actualFiniteOriginalJointResponse_crossing rule scale scalePositive depth clock kind
    (configuration depth) crossing initial clockPositive]
  change originalJointCompactPathLaw
    (actualFiniteIntrinsicJointMark rule scale scalePositive depth (configuration depth) crossing)
    (actualFiniteIntrinsicJointMass rule scale scalePositive depth (configuration depth) crossing) _ = _
  have marksIdentity :
      (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) ∘
        (actualFiniteIntrinsicJointMark rule scale scalePositive depth (configuration depth) crossing) =
      actualFullConfigurationMark rule configuration scale scalePositive depth crossing := by
    funext side
    exact actualFiniteIntrinsicJointMark_configuration_transport rule configuration scale scalePositive depth crossing side
  have massesIdentity :
      (fun side => (actualFiniteIntrinsicJointMass rule scale scalePositive depth
        (configuration depth) crossing side).map
        (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous.measurable.aemeasurable) =
      actualFullConfigurationMass rule configuration scale scalePositive depth crossing := by
    funext side
    exact actualFiniteIntrinsicJointMass_configuration_transport rule configuration scale scalePositive depth crossing side
  have transport := originalJointCompactPathLaw_isometricTransport
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).isometry
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).surjective
    (actualFiniteIntrinsicJointMark rule scale scalePositive depth (configuration depth) crossing)
    (actualFiniteIntrinsicJointMass rule scale scalePositive depth (configuration depth) crossing)
    (actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth (configuration depth)
      crossing initial (clock (configuration depth)) clockPositive kind)
  rw [marksIdentity, massesIdentity] at transport
  exact transport.symm

theorem actualFiniteOriginalJointResponse_selected_identity
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : Fin (rule.generation depth).vertices) :
    actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind
      (stationaryConfiguration rule marks depth, (actualAnnealedSelectedVertex rule marks depth initial).val) =
    actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind
      (stationaryConfiguration rule marks depth, initial) := by
  classical
  unfold actualFiniteOriginalJointResponse
  split_ifs
  · unfold actualFiniteAnnealedCanonicalPathLaw
    simp only [actualFiniteAnnealedInitialVertex_selected_identity rule marks scale scalePositive depth initial]
  all_goals rfl

end
end IGSIII34.Spectral
