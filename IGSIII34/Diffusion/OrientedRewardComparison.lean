import IGSIII34.Diffusion.AllStateRewardComparison
import IGSIII.Mass.CylinderMassLimits

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

def orientedEdgeReward {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (parent : OrientedState) (configuration : Configuration edges) : ℝ :=
  network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration .connected

theorem orientedEdgeReward_connected {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    orientedEdgeReward network .connected configuration = (network.liveCount .connected .connected configuration : ℝ) := by
  rw [(network.liveCount_oriented_split .connected configuration).1]
  simp only [orientedEdgeReward, OrientedState.sourceSelected, OrientedState.targetSelected,
    show (LiveState.connected == LiveState.both) = false from rfl, orientedLiveCount, orientedChildState]
  simp_rw [network.selectedActive_connected configuration crossing]

theorem orientedEdgeReward_both {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    orientedEdgeReward network .both configuration = (network.liveCount .both .connected configuration : ℝ) :=
  (network.liveCount_oriented_split .both configuration).1.symm

theorem orientedEdgeReward_source {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    orientedEdgeReward network .sourceOnly configuration = (network.liveCount .single .connected configuration : ℝ) :=
  (network.liveCount_oriented_split .single configuration).1.symm

theorem orientedEdgeReward_inactive {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : orientedEdgeReward network .inactive configuration = 0 := by
  simp [orientedEdgeReward, orientedLiveCount, orientedChildState, OrientedState.sourceSelected,
    OrientedState.targetSelected, selectedActive, orientedStateOf]

/-- The original B sides are disjoint edge rewards on the same noncrossing
configuration, with no resampling of either side. -/
theorem orientedEdgeReward_joint_both {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (noncrossing : network.crosses configuration = false) :
    orientedEdgeReward network .both configuration = orientedEdgeReward network .sourceOnly configuration +
      orientedEdgeReward network .targetOnly configuration := by
  classical
  unfold orientedEdgeReward orientedLiveCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [network.orientedChildState_connected_iff]
  cases opened : configuration edge <;>
    cases source : (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).1 <;>
    cases target : (network.openGraph configuration).reachableDecide network.target (network.endpoint edge).1 <;>
    simp [OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive, opened, source, target]
  exact (noncrossing_terminal_reachable_disjoint network configuration noncrossing (network.endpoint edge).1
    (((network.openGraph configuration).reachableDecide_eq_true _ _).mp source)
    (((network.openGraph configuration).reachableDecide_eq_true _ _).mp target)).elim

theorem oriented_history_reward_comparison {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ ratio : ℝ, 0 < ratio ∧ ∀ parent : OrientedState,
      ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened,
        Tendsto (fun depth =>
          (orientedEdgeReward (rule.generation depth).network parent
            (Rule.ConfigurationHistory.latest rule depth (path depth)) -
            ratio * (rule.generation depth).network.internalStateMass parent
              (Rule.ConfigurationHistory.latest rule depth (path depth))) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 0) := by
  obtain ⟨ratio, ratioPositive, comparisons⟩ := all_state_edge_vertex_reward_comparison classicalRule
    p positive belowOne fixedPoint
  refine ⟨ratio, ratioPositive, ?_⟩
  intro parent
  cases parent with
  | connected =>
    filter_upwards [comparisons .connected, Rule.ConfigurationHistory.infiniteLaw_crosses rule p positive belowOne fixedPoint true]
      with path comparison crossing
    convert comparison using 1
    ext depth
    rw [orientedEdgeReward_connected _ _ (crossing depth)]
    simp only [internalStateMass, OrientedState.sourceSelected, OrientedState.targetSelected,
      Rule.ConfigurationHistory.vertexMass, show (LiveState.connected == LiveState.both) = false from rfl]
    rw [(rule.generation depth).network.internalSelectedMass_connected _ (crossing depth)]
  | both => simpa [OrientedState.massOpened, orientedEdgeReward_both, internalStateMass,
      OrientedState.sourceSelected, OrientedState.targetSelected, Rule.ConfigurationHistory.vertexMass,
      show (LiveState.both == LiveState.connected) = false from rfl] using comparisons .both
  | sourceOnly => simpa [OrientedState.massOpened, orientedEdgeReward_source, internalStateMass,
      OrientedState.sourceSelected, OrientedState.targetSelected, Rule.ConfigurationHistory.vertexMass,
      show (LiveState.single == LiveState.both) = false from rfl,
      show (LiveState.single == LiveState.connected) = false from rfl] using comparisons .single
  | targetOnly =>
    filter_upwards [comparisons .both, comparisons .single,
      Rule.ConfigurationHistory.infiniteLaw_crosses rule p positive belowOne fixedPoint false]
      with path bothComparison sourceComparison crossing
    have result := bothComparison.sub sourceComparison
    simp only [sub_self] at result
    convert result using 1
    ext depth
    have edgeSplit := orientedEdgeReward_joint_both (rule.generation depth).network _ (crossing depth)
    have vertexSplit := (rule.generation depth).network.internalSelectedMass_disconnected _ (crossing depth)
    simp only [Rule.ConfigurationHistory.vertexMass, beq_self_eq_true,
      show (LiveState.single == LiveState.both) = false from rfl] at *
    rw [← orientedEdgeReward_both, ← orientedEdgeReward_source]
    simp only [internalStateMass, OrientedState.sourceSelected, OrientedState.targetSelected]
    rw [edgeSplit]
    push_cast at vertexSplit
    rw [show ((rule.generation depth).network.internalSelectedMass true true
      (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) =
      (rule.generation depth).network.internalSelectedMass true false
        (Rule.ConfigurationHistory.latest rule depth (path depth)) +
      (rule.generation depth).network.internalSelectedMass false true
        (Rule.ConfigurationHistory.latest rule depth (path depth)) by exact_mod_cast vertexSplit]
    ring
  | inactive =>
    apply Filter.Eventually.of_forall
    intro path
    simpa only [orientedEdgeReward_inactive, internalStateMass_inactive, Nat.cast_zero,
      mul_zero, sub_zero, zero_div] using tendsto_const_nhds

def markedOrientedEdgeMass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) : ℝ :=
  orientedEdgeReward (rule.generation depth).network parent
    (markedGenerationConfiguration rule marks depth address parent.massOpened)

/-- One event covers every address and inherited terminal mask, preserving
the original B coupling and allowing a mask chosen by the ancestor marks. -/
theorem marked_oriented_reward_comparison {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ ratio : ℝ, 0 < ratio ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address parent, Tendsto (fun depth =>
          (markedOrientedEdgeMass rule marks depth address parent -
            ratio * markedOrientedVertexMass rule marks depth address parent) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 0) := by
  obtain ⟨ratio, positiveRatio, comparisons⟩ := oriented_history_reward_comparison classicalRule
    p positive belowOne fixedPoint
  refine ⟨ratio, positiveRatio, ae_all_iff.mpr fun address => ae_all_iff.mpr fun parent => ?_⟩
  have marginal := comparisons parent
  rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint address parent.massOpened] at marginal
  have pulled := ae_of_ae_map (markedHistoryPath_measurable rule address parent.massOpened).aemeasurable marginal
  simpa only [markedOrientedEdgeMass, markedOrientedVertexMass, markedHistoryPath,
    Rule.ConfigurationHistory.latest_ofFine] using pulled

end
end IGSIII34.Diffusion
