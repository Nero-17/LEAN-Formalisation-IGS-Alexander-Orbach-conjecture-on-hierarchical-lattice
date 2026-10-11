import IGSIII34.Spectral.Collars.ActualFiniteConfigurationLawTransport
import IGSIII34.Spectral.Collars.ActualFiniteConfigurationStateTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory
open scoped _root_.Topology

theorem actualFiniteIntrinsicJointResponse_original_discrete
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (clockPositive : 0 < clock (configuration depth))
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Ambient)
    (isometry : Isometry placement) :
    actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock 0 (configuration depth, initial.val) =
    ∫ path, test.value Ambient (jointMeasuredMarkedStateMap placement isometry.continuous
      (actualFullConfigurationState rule configuration scale scalePositive depth crossing)) path
      ∂(discreteCadlagProbabilityCompletion20261011
        (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
        (⟨finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
          (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
          (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing)
          (Measure.dirac initial), inferInstance⟩ : ProbabilityMeasure _)
        (clock (configuration depth)) clockPositive placement : Measure _) := by
  have identity := actualFiniteIntrinsicJointResponse_isometric_placement rule scale scalePositive depth
    test clock 0 (configuration depth) crossing initial.val clockPositive
    (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
    (isometry.comp (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).isometry)
  rw [actualFiniteIntrinsicJointState_placed_configuration_transport rule configuration scale scalePositive depth
    crossing placement isometry.continuous,
    actualFiniteAnnealedPlacedPathLaw_discrete_configuration_transport rule configuration scale scalePositive depth
      crossing initial (clock (configuration depth)) clockPositive placement] at identity
  exact identity

theorem actualFiniteIntrinsicJointResponse_original_weighted
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (clockPositive : 0 < clock (configuration depth))
    (kind : Fin 3) (notDiscrete : kind ≠ 0)
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Ambient)
    (isometry : Isometry placement) :
    actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock kind (configuration depth, initial.val) =
    ∫ path, test.value Ambient (jointMeasuredMarkedStateMap placement isometry.continuous
      (actualFullConfigurationState rule configuration scale scalePositive depth crossing)) path
      ∂(finiteWeightedCadlagProbabilityCompletion20261011
        (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
        (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing)
        (diracProba initial)
        (fun point => if kind = 1 then 1 else
          (degree (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)) point)⁻¹)
        (fun point => by
          split_ifs
          · exact zero_lt_one
          · exact inv_pos.mpr (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing point))
        (clock (configuration depth)) clockPositive placement : Measure _) := by
  have identity := actualFiniteIntrinsicJointResponse_isometric_placement rule scale scalePositive depth
    test clock kind (configuration depth) crossing initial.val clockPositive
    (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
    (isometry.comp (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).isometry)
  rw [actualFiniteIntrinsicJointState_placed_configuration_transport rule configuration scale scalePositive depth
    crossing placement isometry.continuous,
    actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport rule configuration scale scalePositive depth
      crossing initial (clock (configuration depth)) clockPositive kind notDiscrete placement] at identity
  exact identity

end
end IGSIII34.Spectral
