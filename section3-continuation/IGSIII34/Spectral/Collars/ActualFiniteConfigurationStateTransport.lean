import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode
import IGSIII.Chemical.SmallBall.ActualChemicalTerminals

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
    simp only [Bool.false_eq_true, if_false, if_true]
    simp only [actualAnnealedFiniteVertexEquiv, IsometryEquiv.coe_mk]
    set_option backward.defeqAttrib.useBackward true in
      dsimp only [actualFiniteClusterFintype, actualFiniteClusterFinite, actualFiniteClusterMeasurableSpace,
        actualFiniteClusterMetricSpace, actualFiniteClusterDecidableEq, actualFiniteClusterNonempty]
    simp only [ActualFiniteCluster]
    generalize_proofs at *
    generalize stateIdentity : configurationAtDepth rule depth (configuration depth) depth = currentState at *
    have same : currentState = configuration depth :=
      stateIdentity.symm.trans (configurationAtDepth_self rule depth (configuration depth))
    clear stateIdentity
    subst currentState
    change @Measure.map _ _ ⊤ ⊤ id _ = _
    exact @Measure.map_id _ ⊤ _

theorem continuousNonemptyCompactRange_comp_surjective
    {First Last Ambient : Type*} [TopologicalSpace First] [CompactSpace First] [Nonempty First]
    [TopologicalSpace Last] [CompactSpace Last] [Nonempty Last] [TopologicalSpace Ambient]
    (mapping : First → Last) (mappingContinuous : Continuous mapping) (surjective : Function.Surjective mapping)
    (placement : Last → Ambient) (placementContinuous : Continuous placement) :
    continuousNonemptyCompactRange (placement ∘ mapping) (placementContinuous.comp mappingContinuous) =
      continuousNonemptyCompactRange placement placementContinuous := by
  apply NonemptyCompacts.ext
  exact surjective.range_comp placement

def actualFullConfigurationState (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) :
    JointMeasuredMarkedState (ActualFiniteCluster rule configuration scale scalePositive depth) :=
  (continuousNonemptyCompactRange id continuous_id,
    actualFullConfigurationMark rule configuration scale scalePositive depth crossing,
    actualFullConfigurationMass rule configuration scale scalePositive depth crossing)

/-- The ENTIRE intrinsic finite canonical state transports to the full
original configuration state with both original masses and both terminals. -/
theorem actualFiniteIntrinsicJointState_configuration_transport (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) :
    jointMeasuredMarkedStateMap (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
      (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous
      (actualFiniteIntrinsicJointState rule scale scalePositive depth (configuration depth) crossing) =
    actualFullConfigurationState rule configuration scale scalePositive depth crossing := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    change (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) '' Set.range id = Set.range id
    rw [Set.range_id, Set.range_id, Set.image_univ]
    exact Set.range_eq_univ.mpr (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).surjective
  · apply Prod.ext
    · funext side
      exact actualFiniteIntrinsicJointMark_configuration_transport rule configuration scale scalePositive depth crossing side
    · funext counting
      exact actualFiniteIntrinsicJointMass_configuration_transport rule configuration scale scalePositive depth crossing counting

@[simp] theorem actualFullConfigurationMass_counting (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true) :
    (actualFullConfigurationMass rule configuration scale scalePositive depth crossing true : Measure _) =
      actualFiniteClusterMeasure rule configuration scale scalePositive depth := rfl

@[simp] theorem actualFullConfigurationMass_degree (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true) :
    (actualFullConfigurationMass rule configuration scale scalePositive depth (crossing depth) false : Measure _) =
      actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth := rfl

theorem actualFullConfigurationMark_terminal (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true) (side : Bool) :
    actualFullConfigurationMark rule configuration scale scalePositive depth (crossing depth) side =
      IGSIII.Chemical.SmallBall.actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth side := by
  apply Subtype.ext
  rfl

theorem jointMeasuredMarkedStateMap_comp
    {First Middle Last : Type*} [MetricSpace First] [MetricSpace Middle] [MetricSpace Last]
    [MeasurableSpace First] [MeasurableSpace Middle] [MeasurableSpace Last]
    [BorelSpace First] [BorelSpace Middle] [BorelSpace Last]
    (first : First → Middle) (firstContinuous : Continuous first)
    (last : Middle → Last) (lastContinuous : Continuous last) (state : JointMeasuredMarkedState First) :
    jointMeasuredMarkedStateMap (last ∘ first) (lastContinuous.comp firstContinuous) state =
      jointMeasuredMarkedStateMap last lastContinuous (jointMeasuredMarkedStateMap first firstContinuous state) := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    exact (Set.image_image last first (state.1 : Set First)).symm
  · apply Prod.ext
    · rfl
    · funext counting
      apply ProbabilityMeasure.toMeasure_injective
      exact (AEMeasurable.map_map_of_aemeasurable lastContinuous.measurable.aemeasurable
        firstContinuous.measurable.aemeasurable).symm

theorem actualFiniteIntrinsicJointState_placed_configuration_transport (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    {Ambient : Type*} [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Ambient)
    (continuous : Continuous placement) :
    jointMeasuredMarkedStateMap (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
      (continuous.comp (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous)
      (actualFiniteIntrinsicJointState rule scale scalePositive depth (configuration depth) crossing) =
    jointMeasuredMarkedStateMap placement continuous
      (actualFullConfigurationState rule configuration scale scalePositive depth crossing) := by
  rw [jointMeasuredMarkedStateMap_comp
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous
    placement continuous, actualFiniteIntrinsicJointState_configuration_transport]

end
end IGSIII34.Spectral
