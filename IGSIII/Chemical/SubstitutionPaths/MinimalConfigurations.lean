import IGSIII.Chemical.SubstitutionPaths.PivotalPaths
import Universality.Graph.SubstitutionPivotal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Actual simple-path configurations and their descendants

Opening exactly the edges of a simple terminal path makes every open edge
pivotal. Pivotality factors through actual substitution, so each nonempty
descendant configuration is again a minimal crossing configuration. This
gives a pathwise way to prune the address tree without assuming a projection
or a decomposition certificate.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

def MinimalCrossingConfiguration {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) : Prop :=
  network.crosses configuration = true ∧
    ∀ edge, configuration edge = true → network.pivotal configuration edge = true

noncomputable def simplePathConfiguration {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (walk : network.fullGraph.Walk network.source network.target) : Configuration edges :=
  fun edge => decide (s((network.endpoint edge).1, (network.endpoint edge).2) ∈ walk.edges)

theorem simplePathConfiguration_crosses {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (walk : network.fullGraph.Walk network.source network.target) :
    network.crosses (simplePathConfiguration network walk) = true := by
  classical
  apply (network.crosses_eq_true _).mpr
  apply network.reachable_of_walk_edges_open _ walk
  intro bond membership
  have full := SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet membership)
  change bond ∈ (network.openGraph (fun _ => true)).edgeFinset at full
  rw [network.openGraph_edgeFinset] at full
  obtain ⟨edge, _, equality⟩ := Finset.mem_image.mp full
  exact ⟨edge, by simp [simplePathConfiguration, equality, membership], equality⟩

theorem simplePathConfiguration_minimal {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (walk : network.fullGraph.Walk network.source network.target) (path : walk.IsPath) :
    MinimalCrossingConfiguration network (simplePathConfiguration network walk) := by
  classical
  refine ⟨simplePathConfiguration_crosses network walk, ?_⟩
  intro edge retained
  have member : s((network.endpoint edge).1, (network.endpoint edge).2) ∈ walk.edges :=
    of_decide_eq_true retained
  have opening : Function.update (simplePathConfiguration network walk) edge true =
      simplePathConfiguration network walk := Function.update_eq_self_iff.mpr retained.symm
  have closing : network.crosses (Function.update (simplePathConfiguration network walk) edge false) = false := by
    cases result : network.crosses (Function.update (simplePathConfiguration network walk) edge false) with
    | false => rfl
    | true =>
      obtain ⟨other, otherSimple, _⟩ := ((network.crosses_eq_true _).mp result).exists_path_of_dist
      have subset : (other.mapLe (network.openGraph_le_full _)).edges ⊆ walk.edges := by
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
        intro bond membership
        have full := SimpleGraph.mem_edgeFinset.mpr (other.edges_subset_edgeSet membership)
        rw [network.openGraph_edgeFinset] at full
        obtain ⟨otherEdge, openMembership, rfl⟩ := Finset.mem_image.mp full
        have openEdge := (Finset.mem_filter.mp openMembership).2
        by_cases same : otherEdge = edge
        · subst otherEdge; simp at openEdge
        · rw [Function.update_of_ne same] at openEdge
          exact of_decide_eq_true openEdge
      have equality := path.eq_of_edges_subset walk _ (otherSimple.mapLe _) subset
      have otherMember : s((network.endpoint edge).1, (network.endpoint edge).2) ∈ other.edges := by
        rw [← SimpleGraph.Walk.edges_mapLe_eq_edges (network.openGraph_le_full _) other, equality]
        exact member
      have impossible := network.edge_open_of_mem_walk simple _ other edge otherMember
      simp at impossible
  simp only [FiniteNetwork.pivotal, opening, simplePathConfiguration_crosses, closing,
    Bool.not_false, Bool.and_self]

theorem substitute_pivotal_factor
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges) (edge : Fin outerEdges) (child : Fin innerEdges) :
    (outer.substitute inner).pivotal (substitutionConfigurationEquiv cells) (finProdFinEquiv (edge, child)) =
      (outer.pivotal (inner.coarseConfiguration cells) edge && inner.pivotal (cells edge) child) := by
  classical
  have coarse (value : Bool) :
      inner.coarseConfiguration (Function.update cells edge (Function.update (cells edge) child value)) =
        Function.update (inner.coarseConfiguration cells) edge (inner.crosses (Function.update (cells edge) child value)) := by
    funext other
    by_cases same : other = edge
    · subst other; simp [FiniteNetwork.coarseConfiguration]
    · simp [FiniteNetwork.coarseConfiguration, Function.update_of_ne same]
  have monotone : inner.crosses (Function.update (cells edge) child false) = true →
      inner.crosses (Function.update (cells edge) child true) = true := by
    apply inner.crosses_mono
    intro other retained
    by_cases same : other = child
    · subst other; simp
    · simpa [Function.update_of_ne same] using retained
  simp only [FiniteNetwork.pivotal, substitutionConfiguration_update,
    outer.substitute_crosses inner, coarse]
  cases opened : inner.crosses (Function.update (cells edge) child true) <;>
    cases closed : inner.crosses (Function.update (cells edge) child false) <;>
    simp_all

theorem minimal_substitute_children
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges)
    (minimal : MinimalCrossingConfiguration (outer.substitute inner) (substitutionConfigurationEquiv cells)) :
    ∀ edge, (∃ child, cells edge child = true) → MinimalCrossingConfiguration inner (cells edge) := by
  intro edge nonempty
  have childPivotal : ∀ child, cells edge child = true → inner.pivotal (cells edge) child = true := by
    intro child retained
    have pivotal := minimal.2 (finProdFinEquiv (edge, child)) (by
      change cells (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).1
        (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).2 = true
      simpa only [Equiv.symm_apply_apply] using retained)
    rw [substitute_pivotal_factor] at pivotal
    have pair : outer.pivotal (inner.coarseConfiguration cells) edge = true ∧
        inner.pivotal (cells edge) child = true := by simpa only [Bool.and_eq_true] using pivotal
    exact pair.2
  obtain ⟨child, retained⟩ := nonempty
  exact ⟨(inner.pivotal_crosses_eq_state _ child (childPivotal child retained)).trans retained, childPivotal⟩

theorem minimal_substitute_coarse
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges)
    (minimal : MinimalCrossingConfiguration (outer.substitute inner) (substitutionConfigurationEquiv cells)) :
    MinimalCrossingConfiguration outer (inner.coarseConfiguration cells) := by
  refine ⟨by simpa only [outer.substitute_crosses inner] using minimal.1, ?_⟩
  intro edge crossing
  have nonempty : ∃ child, cells edge child = true := by
    by_contra empty
    have allClosed : cells edge = fun _ => false := by
      funext child
      cases value : cells edge child
      · rfl
      · exact False.elim (empty ⟨child, value⟩)
    change inner.crosses (cells edge) = true at crossing
    rw [allClosed, inner.crosses_all_closed] at crossing
    contradiction
  obtain ⟨child, retained⟩ := nonempty
  have pivotal := minimal.2 (finProdFinEquiv (edge, child)) (by
    change cells (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).1
      (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).2 = true
    simpa only [Equiv.symm_apply_apply] using retained)
  rw [substitute_pivotal_factor] at pivotal
  have pair : outer.pivotal (inner.coarseConfiguration cells) edge = true ∧
      inner.pivotal (cells edge) child = true := by simpa only [Bool.and_eq_true] using pivotal
  exact pair.1

end IGSIII.Chemical.Substitution
