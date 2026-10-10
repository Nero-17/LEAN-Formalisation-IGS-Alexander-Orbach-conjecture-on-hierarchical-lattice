import IGSIII.Chemical.SubstitutionPaths.MinimalConfigurations
import IGSIII.Chemical.SubstitutionPaths.CoherentHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem networkEquivalence_configuration_update
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (edge : Fin firstEdges) (opened : Bool) :
    equivalence.configuration (Function.update configuration edge opened) =
      Function.update (equivalence.configuration configuration) (equivalence.edge edge) opened := by
  classical
  funext other
  by_cases same : other = equivalence.edge edge
  · subst other; simp [NetworkEquivalence.configuration]
  · have different : equivalence.edge.symm other ≠ edge := by
      intro equality
      exact same (equivalence.edge.symm_apply_eq.mp equality)
    simp [NetworkEquivalence.configuration, Function.update_of_ne same, Function.update_of_ne different]

theorem networkEquivalence_pivotal
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (edge : Fin firstEdges) :
    second.pivotal (equivalence.configuration configuration) (equivalence.edge edge) =
      first.pivotal configuration edge := by
  simp only [FiniteNetwork.pivotal, ← networkEquivalence_configuration_update,
    equivalence.crosses]

theorem networkEquivalence_minimal
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (minimal : MinimalCrossingConfiguration first configuration) :
    MinimalCrossingConfiguration second (equivalence.configuration configuration) := by
  refine ⟨by simpa only [equivalence.crosses] using minimal.1, ?_⟩
  intro edge retained
  obtain ⟨original, rfl⟩ := equivalence.edge.surjective edge
  rw [networkEquivalence_pivotal]
  apply minimal.2 original
  simpa only [NetworkEquivalence.configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using retained

theorem minimal_generation_children (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation (depth + 1)).network configuration) :
    ∀ edge, (∃ child, generationTopCells rule depth configuration edge child = true) →
      MinimalCrossingConfiguration (rule.generation depth).network
        (generationTopCells rule depth configuration edge) := by
  have transported := networkEquivalence_minimal (rule.generationTopDecomposition depth) configuration minimal
  rw [← configuration_of_topCells] at transported
  exact minimal_substitute_children rule.network (rule.generation depth).network _ transported

theorem minimal_generation_root (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation (depth + 1)).network configuration) :
    MinimalCrossingConfiguration rule.network (generationRootConfiguration rule depth configuration) := by
  have transported := networkEquivalence_minimal (rule.generationTopDecomposition depth) configuration minimal
  rw [← configuration_of_topCells] at transported
  exact minimal_substitute_coarse rule.network (rule.generation depth).network _ transported

theorem minimal_generation_child_nonempty_iff (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation (depth + 1)).network configuration)
    (edge : Fin rule.edges) :
    (∃ child, generationTopCells rule depth configuration edge child = true) ↔
      generationRootConfiguration rule depth configuration edge = true := by
  constructor
  · intro nonempty
    exact (minimal_generation_children rule depth configuration minimal edge nonempty).1
  · intro crossing
    by_contra empty
    have allClosed : generationTopCells rule depth configuration edge = fun _ => false := by
      funext child
      cases value : generationTopCells rule depth configuration edge child
      · rfl
      · exact False.elim (empty ⟨child, value⟩)
    change (rule.generation depth).network.crosses (generationTopCells rule depth configuration edge) = true at crossing
    rw [allClosed, (rule.generation depth).network.crosses_all_closed] at crossing
    contradiction

def openEdges {edges : ℕ} (configuration : Configuration edges) : Finset (Fin edges) :=
  Finset.univ.filter fun edge => configuration edge = true

theorem openEdges_card {edges : ℕ} (configuration : Configuration edges) :
    (openEdges configuration).card = openCount configuration := rfl

theorem crossing_two_open_edges {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    2 ≤ (openEdges configuration).card := by
  have bound := network.distance_le_openCount configuration crossing
  rw [openEdges_card]
  omega

theorem generation_openCount_topCells (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) :
    openCount configuration = ∑ edge : Fin rule.edges,
      openCount (generationTopCells rule depth configuration edge) := by
  classical
  have countRelabel : openCount configuration =
      openCount ((rule.generationTopDecomposition depth).configuration configuration) := by
    unfold openCount
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    simpa only [NetworkEquivalence.configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
      (rule.generationTopDecomposition depth).edge.sum_comp (fun edge =>
        if (rule.generationTopDecomposition depth).configuration configuration edge = true then (1 : ℕ) else 0)
  rw [countRelabel, ← configuration_of_topCells]
  unfold openCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (finProdFinEquiv.symm.sum_comp (fun pair : Fin rule.edges × Fin (rule.generation depth).edges =>
    if generationTopCells rule depth configuration pair.1 pair.2 = true then (1 : ℕ) else 0)).trans
      (Fintype.sum_prod_type _)

end IGSIII.Chemical.Substitution
