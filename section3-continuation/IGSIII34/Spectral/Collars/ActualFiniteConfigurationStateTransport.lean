import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option backward.dsimp.instances true
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory TopologicalSpace
open scoped _root_.Topology

def actualFullConfigurationMark (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) (side : Bool) :
    ActualFiniteCluster rule configuration scale scalePositive depth :=
  ⟨plantedVertex (rule.generation depth).network side, by
    cases side with
    | false => exact ((rule.generation depth).network.crosses_eq_true _).mp crossing
    | true => exact SimpleGraph.Reachable.refl _⟩

theorem actualFiniteIntrinsicJointMark_configuration_transport (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) (side : Bool) :
    actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth
      (actualFiniteIntrinsicJointMark rule scale scalePositive depth (configuration depth) crossing side) =
    actualFullConfigurationMark rule configuration scale scalePositive depth crossing side := by
  apply Subtype.ext
  rfl

def actualFullConfigurationMass (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) (counting : Bool) :
    ProbabilityMeasure (ActualFiniteCluster rule configuration scale scalePositive depth) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) crossing
  exact if counting then ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩ else
    ⟨degreeMeasure (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)), inferInstance⟩

theorem actualFiniteIntrinsicJointMass_configuration_transport (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) (counting : Bool) :
    (actualFiniteIntrinsicJointMass rule scale scalePositive depth (configuration depth) crossing counting).map
      (measurable_of_finite (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)).aemeasurable =
    actualFullConfigurationMass rule configuration scale scalePositive depth crossing counting := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  cases counting <;> unfold actualFiniteIntrinsicJointMass actualFullConfigurationMass
  all_goals
    simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true]
    simp only [actualAnnealedFiniteVertexEquiv, IsometryEquiv.coe_mk]
    set_option backward.defeqAttrib.useBackward true in
      dsimp only [actualFiniteClusterFintype, actualFiniteClusterFinite, actualFiniteClusterMeasurableSpace,
        actualFiniteClusterMetricSpace, actualFiniteClusterDecidableEq, actualFiniteClusterNonempty]
    simp only [ActualFiniteCluster, configurationAtDepth, Function.update]
    generalize_proofs at *
    generalize decision : instDecidableEqNat depth depth = currentDecision at *
    cases currentDecision with
    | isTrue identity => simpa only [Measure.map_id]
    | isFalse contradiction => exact (contradiction rfl).elim

theorem continuousNonemptyCompactRange_comp_surjective
    {First Last Ambient : Type*} [TopologicalSpace First] [CompactSpace First] [Nonempty First]
    [TopologicalSpace Last] [CompactSpace Last] [Nonempty Last] [TopologicalSpace Ambient]
    (mapping : First → Last) (mappingContinuous : Continuous mapping) (surjective : Function.Surjective mapping)
    (placement : Last → Ambient) (placementContinuous : Continuous placement) :
    continuousNonemptyCompactRange (placement ∘ mapping) (placementContinuous.comp mappingContinuous) =
      continuousNonemptyCompactRange placement placementContinuous := by
  apply NonemptyCompacts.ext
  exact surjective.range_comp placement

end
end IGSIII34.Spectral
