import IGSIII34.Diffusion.FiniteClocks
import IGSIII.Mass.MarkedConnectedPopulation
import IGSIII.Geometry.ActualFiniteMass
import Universality.Percolation.ClusterMass

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

/-- Edges of the actual retained root cluster; every indexed microscopic edge
is included exactly when open and reachable from the root. -/
def ClusterEdge {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :=
  {edge : Fin edges // configuration edge = true ∧
    network.active .connected configuration (network.endpoint edge).1 = true}

instance clusterEdge_fintype {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Fintype (ClusterEdge network configuration) := by
  classical
  unfold ClusterEdge
  infer_instance

theorem clusterEdge_card {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    Fintype.card (ClusterEdge network configuration) = network.liveCount .connected .connected configuration := by
  classical
  rw [← network.clusterEdgeCount_eq_liveCount]
  simp [ClusterEdge, Fintype.card_subtype, clusterEdgeCount]

def clusterEndpoint {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : ClusterEdge network configuration → Fin vertices × Fin vertices :=
  fun edge => network.endpoint edge.val

theorem actual_degree_reward {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    ∑ vertex, degree (clusterEndpoint network configuration) vertex =
      2 * (network.liveCount .connected .connected configuration : ℝ) := by
  rw [degree_sum, clusterEdge_card]

theorem actual_degree_half_mass {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (test : Fin vertices → ℝ) :
    ∑ vertex, degreeWeight (clusterEndpoint network configuration) vertex * test vertex =
      (∑ edge : ClusterEdge network configuration,
        (test (network.endpoint edge.val).1 + test (network.endpoint edge.val).2)) /
        (2 * network.liveCount .connected .connected configuration) := by
  rw [degreeWeight_test, clusterEdge_card]
  rfl

/-- Edge and full vertex counts share the *same* positive Perron random
variable on the original independent innovation space. The additional factor
of the Perron root records `generation n` versus Section 2 root-level `n+1`. -/
theorem actual_joint_edge_vertex_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (left : LiveState → ℝ) (coefficient : ℝ)
      (limit : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < left .connected ∧ 0 < coefficient ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < limit marks ∧
        Tendsto (fun depth => ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) *
            (limit marks * left .connected))) ∧
        Tendsto (fun depth => (markedComponentVertexMass rule marks depth [] + 2) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) *
            (coefficient * limit marks))) := by
  obtain ⟨right, left, coefficient, limit, _, _, _, leftPositive, _, _, _, coefficientPositive,
    _, _, _, limitPositive, coordinates, vertices⟩ :=
    classicalRule.three_state_mass_perron p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨left, coefficient, fun marks => limit (markedHistoryPath rule [] true marks),
    leftPositive .connected, coefficientPositive, ?_⟩
  have properties := limitPositive.and (coordinates.and vertices)
  rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint [] true] at properties
  have actual := ae_of_ae_map (markedHistoryPath_measurable rule [] true).aemeasurable properties
  filter_upwards [actual, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks properties crossing
  refine ⟨properties.1, ?_, ?_⟩
  · have shifted := ((properties.2.1 .connected).comp (tendsto_add_atTop_nat 1)).const_mul
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    convert shifted using 1
    ext depth
    simp only [Function.comp_apply, Rule.ConfigurationHistory.rootLevelPopulation_succ,
      Rule.ConfigurationHistory.weightedPopulation, markedHistoryPath,
      Rule.ConfigurationHistory.latest_ofFine, FiniteNetwork.liveResponse_eq,
      mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, mul_zero, pow_succ]
    field_simp [radiusPositive.ne']
  · have shifted := (properties.2.2.comp (tendsto_add_atTop_nat 1)).const_mul
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    convert shifted using 1
    ext depth
    simp only [Function.comp_apply, Rule.ConfigurationHistory.rootLevelVertexCount_succ,
      Rule.ConfigurationHistory.vertexMass, markedHistoryPath, Rule.ConfigurationHistory.latest_ofFine,
      markedComponentVertexMass, componentEdgeAddress, List.map_nil, retainedComponentState,
      retainedComponentStateFrom, markedOrientedVertexMass, internalStateMass, OrientedState.sourceSelected,
      OrientedState.targetSelected, OrientedState.massOpened,
      decide_true,
      show (LiveState.connected == LiveState.both) = false from rfl]
    rw [(rule.generation depth).network.internalSelectedMass_connected _
      (markedGenerationConfiguration_crosses rule marks crossing depth [] true)]
    rw [pow_succ]
    field_simp [radiusPositive.ne']
    <;> ring

end
end IGSIII34.Diffusion
