import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.ResistanceLimit IGSIII34.Diffusion MeasureTheory
open scoped _root_.Topology

theorem actualFiniteAnnealedPlacedPathLaw_discrete_configuration
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
  simp only [actualAnnealedFiniteVertexEquiv, Function.comp_def, ActualFiniteCluster,
    configurationAtDepth, Function.update, dif_pos rfl]
  rfl

end
end IGSIII34.Spectral
