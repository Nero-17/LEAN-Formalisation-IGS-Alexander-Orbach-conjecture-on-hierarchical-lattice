import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode
import Mathlib.Tactic.BDSimp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.dsimp.instances true
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.ResistanceLimit IGSIII34.Diffusion MeasureTheory
open scoped _root_.Topology

theorem actualFiniteAnnealedPlacedPathLaw_discrete_configuration_transport
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (clock : ℝ) (clockPositive : 0 < clock)
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Space) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (configuration depth) crossing initial.val
      clock clockPositive 0 (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) =
    discreteCadlagProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
      (⟨finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
        (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing)
        (Measure.dirac initial), inferInstance⟩ : ProbabilityMeasure _)
      clock clockPositive placement := by
  classical
  simp only [actualFiniteAnnealedPlacedPathLaw, dite_true]
  have retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source initial.val := initial.property
  simp only [actualFiniteAnnealedInitialVertex, dif_pos retained]
  simp only [actualAnnealedFiniteVertexEquiv, Function.comp_def, IsometryEquiv.coe_mk]
  set_option backward.defeqAttrib.useBackward true in
    dsimp only [actualFiniteClusterFintype, actualFiniteClusterFinite, actualFiniteClusterMeasurableSpace,
      actualFiniteClusterMetricSpace, actualFiniteClusterDecidableEq, actualFiniteClusterNonempty]
  simp only [ActualFiniteCluster, configurationAtDepth, Function.update]
  generalize_proofs at *
  generalize decision : instDecidableEqNat depth depth = currentDecision at *
  cases currentDecision with
  | isTrue identity => rfl
  | isFalse contradiction => exact (contradiction rfl).elim

/-- Exact configuration transport of the original exponential holding walk,
including rate-one and inverse-degree clocks, on the same finite labels. -/
theorem actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) (notDiscrete : kind ≠ 0)
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Space) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (configuration depth) crossing initial.val
      clock clockPositive kind (placement ∘ actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) =
    finiteWeightedCadlagProbabilityCompletion20261011
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
      clock clockPositive placement := by
  classical
  simp only [actualFiniteAnnealedPlacedPathLaw, dif_neg notDiscrete]
  have retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source initial.val := initial.property
  simp only [actualFiniteAnnealedInitialVertex, dif_pos retained]
  unfold diracProba
  simp only [actualAnnealedFiniteVertexEquiv, Function.comp_def, IsometryEquiv.coe_mk]
  set_option backward.defeqAttrib.useBackward true in
    dsimp only [actualFiniteClusterFintype, actualFiniteClusterFinite, actualFiniteClusterMeasurableSpace,
      actualFiniteClusterMetricSpace, actualFiniteClusterDecidableEq, actualFiniteClusterNonempty]
  simp only [ActualFiniteCluster, configurationAtDepth, Function.update]
  generalize_proofs at *
  generalize decision : instDecidableEqNat depth depth = currentDecision at *
  cases currentDecision with
  | isTrue identity => rfl
  | isFalse contradiction => exact (contradiction rfl).elim

end
end IGSIII34.Spectral

