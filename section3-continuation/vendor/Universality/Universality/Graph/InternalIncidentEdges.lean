import Universality.Graph.ClassicalRule
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

def incidentEdges (R : FiniteNetwork vertices edges) (vertex : Fin vertices) : Finset (Fin edges) :=
  Finset.univ.filter fun edge => (R.endpoint edge).1 = vertex ∨ (R.endpoint edge).2 = vertex

theorem exists_incident_edge_of_reachable (R : FiniteNetwork vertices edges)
    (vertex : Fin vertices) (hvertex : vertex ≠ R.source)
    (hconnected : R.fullGraph.Reachable R.source vertex) :
    ∃ edge, (R.endpoint edge).1 = vertex ∨ (R.endpoint edge).2 = vertex := by
  obtain ⟨walk⟩ := hconnected.symm
  cases walk with
  | nil => exact (hvertex rfl).elim
  | cons hadj tail =>
    obtain ⟨_, edge, _, hpair | hpair⟩ := hadj
    · exact ⟨edge, Or.inl (congrArg Prod.fst hpair)⟩
    · exact ⟨edge, Or.inr (congrArg Prod.snd hpair)⟩

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

theorem Classical.internal_vertex_two_neighbors {rule : Rule} (h : rule.Classical)
    (vertex : Fin rule.vertices) (hsource : vertex ≠ rule.network.source)
    (htarget : vertex ≠ rule.network.target) :
    ∃ first second, rule.network.fullGraph.Adj vertex first ∧
      rule.network.fullGraph.Adj vertex second ∧ first ≠ second := by
  obtain ⟨edge, hfirst | hsecond⟩ :=
    rule.network.exists_incident_edge_of_reachable vertex hsource (h.connected vertex)
  all_goals
    obtain ⟨walk, hpath, hmem⟩ := h.canonical edge
    have hsupport : vertex ∈ walk.support := by
      first
      | simpa only [hfirst] using walk.fst_mem_support_of_mem_edges hmem
      | simpa only [hsecond] using walk.snd_mem_support_of_mem_edges hmem
    have hnot : ¬ (rule.network.fullGraph.neighborSet vertex).Subsingleton := by
      intro hsingle
      exact hpath.isTrail.not_mem_support_of_subsingleton_neighborSet hsource htarget hsingle hsupport
    obtain ⟨first, hfirst, second, hsecond, hne⟩ := Set.not_subsingleton_iff.mp hnot
    exact ⟨first, second, hfirst, hsecond, hne⟩

theorem Classical.internal_vertex_two_incident_edges {rule : Rule} (h : rule.Classical)
    (vertex : Fin rule.vertices) (hsource : vertex ≠ rule.network.source)
    (htarget : vertex ≠ rule.network.target) :
    ∃ first second : Fin rule.edges, first ≠ second ∧
      first ∈ rule.network.incidentEdges vertex ∧ second ∈ rule.network.incidentEdges vertex := by
  obtain ⟨firstNeighbor, secondNeighbor, hfirst, hsecond, hne⟩ :=
    h.internal_vertex_two_neighbors vertex hsource htarget
  obtain ⟨hfirstNe, first, _, hfirstPair⟩ := hfirst
  obtain ⟨hsecondNe, second, _, hsecondPair⟩ := hsecond
  have hedges : first ≠ second := by
    intro heq
    subst second
    rcases hfirstPair with hfirstPair | hfirstPair <;>
      rcases hsecondPair with hsecondPair | hsecondPair <;>
      rw [hfirstPair] at hsecondPair <;> simp_all only [Prod.mk.injEq]
  refine ⟨first, second, hedges, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hfirstPair with hpair | hpair
    · exact Or.inl (congrArg Prod.fst hpair)
    · exact Or.inr (congrArg Prod.snd hpair)
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hsecondPair with hpair | hpair
    · exact Or.inl (congrArg Prod.fst hpair)
    · exact Or.inr (congrArg Prod.snd hpair)

theorem Classical.internal_incidentEdges_card_ge_two {rule : Rule} (h : rule.Classical)
    (vertex : Fin rule.vertices) (hsource : vertex ≠ rule.network.source)
    (htarget : vertex ≠ rule.network.target) :
    2 ≤ (rule.network.incidentEdges vertex).card := by
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    h.internal_vertex_two_incident_edges vertex hsource htarget
  have hsubset : {first, second} ⊆ rule.network.incidentEdges vertex := by
    intro edge hedge
    rcases Finset.mem_insert.mp hedge with rfl | hedge
    · exact hfirst
    · have heq := Finset.mem_singleton.mp hedge
      simpa only [heq] using hsecond
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsubset

end
end Universality.Rule
