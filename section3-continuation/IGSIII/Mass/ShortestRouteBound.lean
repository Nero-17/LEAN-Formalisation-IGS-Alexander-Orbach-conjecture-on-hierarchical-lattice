import IGSIII.Mass.FourStateMassPerron
import Universality.Graph.CrossingOpenCount

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix
open scoped BigOperators

variable {vertices edges : ℕ}

/-- Keep precisely the open edges of the original source component. -/
noncomputable def sourceComponentConfiguration (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Configuration edges :=
  fun edge => configuration edge &&
    (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).1

theorem sourceComponentConfiguration_reachable (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (vertex : Fin vertices) :
    (network.openGraph (network.sourceComponentConfiguration configuration)).Reachable network.source vertex ↔
      (network.openGraph configuration).Reachable network.source vertex := by
  have inclusion : network.openGraph (network.sourceComponentConfiguration configuration) ≤
      network.openGraph configuration := by
    intro first second adjacency
    obtain ⟨distinct, edge, opened, endpoints⟩ := adjacency
    have retained : configuration edge = true ∧
        (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).1 = true := by
      simpa only [sourceComponentConfiguration, Bool.and_eq_true] using opened
    exact ⟨distinct, edge, retained.1, endpoints⟩
  constructor
  · exact SimpleGraph.Reachable.mono inclusion
  · intro reachable
    obtain ⟨walk⟩ := reachable
    have lift : ∀ {first last : Fin vertices} (walk : (network.openGraph configuration).Walk first last),
        (network.openGraph configuration).Reachable network.source first →
        (network.openGraph (network.sourceComponentConfiguration configuration)).Reachable first last := by
      intro first last walk
      induction walk with
      | nil => exact fun _ => .refl _
      | @cons first second last adjacency tail induction_hypothesis =>
        intro first_reachable
        have second_reachable := first_reachable.trans adjacency.reachable
        obtain ⟨distinct, edge, opened, endpoints⟩ := adjacency
        have edge_reachable : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 := by
          rcases endpoints with endpoints | endpoints
          · simpa only [endpoints] using first_reachable
          · simpa only [endpoints] using second_reachable
        have retained : network.sourceComponentConfiguration configuration edge = true := by
          simpa only [sourceComponentConfiguration, Bool.and_eq_true] using
            And.intro opened (((network.openGraph configuration).reachableDecide_eq_true _ _).mpr edge_reachable)
        exact (show (network.openGraph (network.sourceComponentConfiguration configuration)).Adj first second from
          ⟨distinct, edge, retained, endpoints⟩).reachable.trans
            (induction_hypothesis second_reachable)
    exact lift walk (.refl _)

theorem sourceComponentConfiguration_openCount (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    openCount (network.sourceComponentConfiguration configuration) =
      network.liveCount .connected .connected configuration := by
  unfold openCount liveCount
  congr 1
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sourceComponentConfiguration,
    Bool.and_eq_true, network.childState_connected_iff, network.active_connected]

/-- A crossing component contains a terminal route, including after all
unrelated open components have been removed. -/
theorem distance_le_connected_liveCount (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    network.fullGraph.dist network.source network.target ≤ network.liveCount .connected .connected configuration := by
  rw [← network.sourceComponentConfiguration_openCount]
  apply network.distance_le_openCount
  exact (network.crosses_eq_true _).mpr
    ((network.sourceComponentConfiguration_reachable configuration network.target).mpr
      ((network.crosses_eq_true _).mp crossing))

theorem distance_le_orientedMassMatrix_connected (network : FiniteNetwork vertices edges)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (reliability_positive : 0 < network.reliability p)
    (reliability_below_one : network.reliability p < 1) :
    (network.fullGraph.dist network.source network.target : ℝ) ≤
      network.orientedMassMatrix p .connected .connected := by
  have count_bound (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
      (network.fullGraph.dist network.source network.target : ℝ) ≤
        network.orientedLiveCount true false configuration .connected := by
    have erase := (network.liveCount_oriented_split .connected configuration).1
    simp only [show (LiveState.connected == .both) = false from rfl] at erase
    rw [← erase]
    exact_mod_cast network.distance_le_connected_liveCount configuration crossing
  calc
    _ = ∑ configuration, network.conditionalCellWeight p true configuration *
        (network.fullGraph.dist network.source network.target : ℝ) := by
      rw [← Finset.sum_mul, network.sum_conditionalCellWeight p reliability_positive reliability_below_one, one_mul]
    _ ≤ network.orientedMassMatrix p .connected .connected := by
      apply Finset.sum_le_sum
      intro configuration _
      change network.conditionalCellWeight p true configuration * _ ≤
        network.conditionalCellWeight p true configuration * network.orientedLiveCount true false configuration .connected
      by_cases crossing : network.crosses configuration = true
      · exact mul_le_mul_of_nonneg_left (count_bound configuration crossing)
          (network.conditionalCellWeight_nonneg positive.le below_one.le _ _)
      · simp [conditionalCellWeight, crossing]

end Universality.FiniteNetwork

namespace Universality.Rule

open FiniteNetwork Matrix

/-- The four-state Perron root dominates the deterministic terminal distance. -/
theorem Classical.distance_le_mass_spectralRadius {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
  obtain ⟨_, right, right_positive, _, eigenvector⟩ :=
    classicalRule.four_type_mass_spectralRadius p positive below_one fixed_point
  have diagonal_bound : rule.network.orientedMassMatrix p .connected .connected * right .connected ≤
      (rule.network.orientedMassMatrix p *ᵥ right) .connected := by
    change _ ≤ ∑ state, rule.network.orientedMassMatrix p .connected state * right state
    exact Finset.single_le_sum (f := fun state => rule.network.orientedMassMatrix p .connected state * right state)
      (fun state _ => mul_nonneg (rule.network.orientedMassMatrix_nonnegative p positive.le below_one.le _ _)
        (right_positive state).le) (Finset.mem_univ MassLiveState.connected)
  rw [eigenvector] at diagonal_bound
  have entry_bound := (mul_le_mul_iff_left₀ (right_positive .connected)).mp diagonal_bound
  exact (rule.network.distance_le_orientedMassMatrix_connected p positive below_one
    (by rwa [fixed_point]) (by rwa [fixed_point])).trans entry_bound

end Universality.Rule
