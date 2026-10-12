import IGSIII34.Diffusion.ActualCountingClockBoundsCompletion
import IGSIII34.Diffusion.ElectricalCountingProjectionCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution IGSIII34.ResistanceLimit
open MeasureTheory Filter
open scoped _root_.Topology

def actualCountingClockCenteredForcingCompletion (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (vertex : ActualFiniteCluster rule configuration scale scalePositive depth) : ℝ :=
  finiteCountingClockDensityCompletion (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)) vertex - 1

theorem ae_actualCountingClock_density_bound_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (scale : ℝ) (scalePositive : 0 < scale), ∃ bound : ℝ, 0 < bound ∧ ∀ depth,
      ∀ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth,
        (0 ≤ finiteCountingClockDensityCompletion
          (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) vertex ∧
        finiteCountingClockDensityCompletion
          (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) vertex ≤ bound) ∧
        |actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks) scale scalePositive depth vertex| ≤ bound + 1 := by
  filter_upwards [ae_actual_edge_vertex_ratio_bounded_completion rule classicalRule p positive belowOne fixedPoint,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks bounded crossing
  intro scale scalePositive
  obtain ⟨bound, boundPositive, bounded⟩ := bounded scale scalePositive
  refine ⟨bound, boundPositive, ?_⟩
  intro depth vertex
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks depth)
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
  have degreePositive := cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks depth)
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
  have densityPositive := finiteCountingClockDensity_nonnegative_completion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) vertex
  have densityUpper := (finiteCountingClockDensity_upper_completion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) vertex (degreePositive vertex)).trans (bounded depth)
  refine ⟨⟨densityPositive, densityUpper⟩, ?_⟩
  unfold actualCountingClockCenteredForcingCompletion
  exact (finiteCenteredCountingClock_bound_completion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) degreePositive vertex).trans
      (add_le_add_left (bounded depth) 1)

end
end IGSIII34.Diffusion
