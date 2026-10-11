import IGSIII34.Resistance.IntegrationByParts
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]

def descendingPotentialStepCompletion20261011 (network : FiniteNetwork Vertex Edge)
    (potential : Vertex → ℝ) (first last : Vertex) : Prop :=
  network.graph.Adj first last ∧ potential last < potential first

theorem descendingPotentialReachable_le_completion20261011 (network : FiniteNetwork Vertex Edge)
    (potential : Vertex → ℝ) {first last : Vertex}
    (reachable : Relation.ReflTransGen (descendingPotentialStepCompletion20261011 network potential) first last) :
    potential last ≤ potential first := by
  induction reachable with
  | refl => exact le_rfl
  | tail _ step previous => exact step.2.le.trans previous

theorem descendingPotentialReachable_simple_path_completion20261011 (network : FiniteNetwork Vertex Edge)
    (potential : Vertex → ℝ) {first last : Vertex}
    (reachable : Relation.ReflTransGen (descendingPotentialStepCompletion20261011 network potential) first last) :
    ∃ path : network.graph.Walk first last, path.IsPath ∧
      ∀ vertex ∈ path.support, potential last ≤ potential vertex ∧ potential vertex ≤ potential first := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨.nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
    intro vertex member
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
    subst vertex
    exact ⟨le_rfl, le_rfl⟩
  | @head first middle step reachable previous =>
    obtain ⟨path, simple, bounds⟩ := previous
    have absent : first ∉ path.support := by
      intro member
      have upper := (bounds first member).2
      linarith [step.2]
    refine ⟨.cons step.1 path, simple.cons absent, ?_⟩
    intro vertex member
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨(descendingPotentialReachable_le_completion20261011 network potential reachable).trans step.2.le, le_rfl⟩
    · exact ⟨(bounds vertex member).1, (bounds vertex member).2.trans step.2.le⟩

theorem descendingPotentialReachable_path_through_edge_completion20261011
    (network : FiniteNetwork Vertex Edge) (potential : Vertex → ℝ)
    (first last : Vertex) (adjacent : network.graph.Adj first last) (decrease : potential last < potential first)
    (before : Relation.ReflTransGen (descendingPotentialStepCompletion20261011 network potential) network.source first)
    (after : Relation.ReflTransGen (descendingPotentialStepCompletion20261011 network potential) last network.target) :
    ∃ path : network.graph.Walk network.source network.target,
      path.IsPath ∧ s(first, last) ∈ path.edges := by
  obtain ⟨prefixPath, prefixSimple, prefixBounds⟩ := descendingPotentialReachable_simple_path_completion20261011 network potential before
  obtain ⟨suffixPath, suffixSimple, suffixBounds⟩ := descendingPotentialReachable_simple_path_completion20261011 network potential after
  refine ⟨prefixPath.append (.cons adjacent suffixPath), ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons, List.tail_cons]
    apply List.Nodup.append prefixSimple.support_nodup suffixSimple.support_nodup
    intro vertex prefixMember suffixMember
    have lower := (prefixBounds vertex prefixMember).1
    have upper := (suffixBounds vertex suffixMember).2
    linarith
  · simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      List.mem_append, List.mem_cons, true_or, or_true]

end
end IGSIII34.Resistance.FiniteNetwork
