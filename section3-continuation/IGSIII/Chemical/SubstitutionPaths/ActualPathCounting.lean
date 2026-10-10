import IGSIII.Chemical.SubstitutionPaths.PathTrieReconstruction
import Universality.Graph.ClassicalSubstitution
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Exponential counting of actual hierarchical simple terminal paths

No path encoding is supplied as a hypothesis. The actual finest edge set
determines an injective address trie. Its nonempty descendant configurations
are minimal crossing configurations, so scale greater than one excludes
unary nodes. First-child/next-sibling coding then gives a constant depending
only on the original rule, uniformly in the microscopic generation.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Chemical.PathCounting

noncomputable def minimalConfigurationsOfSize (rule : Rule) (depth size : ℕ) :
    Finset (Configuration (rule.generation depth).edges) := by
  classical
  exact Finset.univ.filter fun configuration =>
    MinimalCrossingConfiguration (rule.generation depth).network configuration ∧ openCount configuration = size

theorem minimal_configurations_count (rule : Rule)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (depth size : ℕ) :
    (minimalConfigurationsOfSize rule depth size).card ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  by_cases positive : 0 < size
  · let trees := (minimalConfigurationsOfSize rule depth size).image (configurationSupportTree rule depth)
    have nodeBound : ∀ tree ∈ trees, tree.numNodes ≤ 2 * size - 1 := by
      intro tree membership
      obtain ⟨configuration, configurationMembership, rfl⟩ := Finset.mem_image.mp membership
      have conditions := (Finset.mem_filter.mp configurationMembership).2
      have bound := configurationSupportTree_node_bound rule scale depth configuration conditions.1
      rwa [conditions.2] at bound
    have count := binaryTree_family_card_le_exponential trees positive nodeBound
    have imageCard : trees.card = (minimalConfigurationsOfSize rule depth size).card :=
      Finset.card_image_of_injective _ (configurationSupportTree_injective rule depth)
    simpa only [imageCard, Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using count
  · have zero : size = 0 := by omega
    have empty : minimalConfigurationsOfSize rule depth size = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro configuration membership
      have conditions := (Finset.mem_filter.mp membership).2
      have closed := (openCount_eq_zero_iff configuration).mp (conditions.2.trans zero)
      obtain ⟨edge, retained⟩ := minimal_configuration_nonempty _ _ conditions.1
      rw [closed] at retained
      contradiction
    simp [empty]

noncomputable def pathEdgeConfiguration {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (path : Finset (Sym2 (Fin vertices))) : Configuration edges :=
  fun edge => decide (s((network.endpoint edge).1, (network.endpoint edge).2) ∈ path)

theorem pathEdgeConfiguration_image {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (path : Finset (Sym2 (Fin vertices)))
    (membership : path ∈ graphPathSets network.fullGraph network.source network.target) :
    (openEdges (pathEdgeConfiguration network path)).image
      (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)) = path := by
  classical
  obtain ⟨walk, _, rfl⟩ := (mem_graphPathSets _ _ _ path).mp membership
  ext bond
  constructor
  · intro member
    obtain ⟨edge, edgeMembership, rfl⟩ := Finset.mem_image.mp member
    simpa only [openEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      pathEdgeConfiguration, decide_eq_true_eq] using edgeMembership
  · intro member
    have full := SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet (List.mem_toFinset.mp member))
    change bond ∈ (network.openGraph (fun _ => true)).edgeFinset at full
    rw [network.openGraph_edgeFinset] at full
    obtain ⟨edge, _, equality⟩ := Finset.mem_image.mp full
    refine Finset.mem_image.mpr ⟨edge, ?_, equality⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [pathEdgeConfiguration, decide_eq_true_eq]
    exact equality.symm ▸ member

theorem pathEdgeConfiguration_openCount {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (path : Finset (Sym2 (Fin vertices)))
    (membership : path ∈ graphPathSets network.fullGraph network.source network.target) :
    openCount (pathEdgeConfiguration network path) = path.card := by
  calc
    _ = (openEdges (pathEdgeConfiguration network path)).card := rfl
    _ = ((openEdges (pathEdgeConfiguration network path)).image
        (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2))).card :=
      (Finset.card_image_of_injective _ simple).symm
    _ = _ := congrArg Finset.card (pathEdgeConfiguration_image network path membership)

theorem pathEdgeConfiguration_minimal {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (path : Finset (Sym2 (Fin vertices)))
    (membership : path ∈ graphPathSets network.fullGraph network.source network.target) :
    MinimalCrossingConfiguration network (pathEdgeConfiguration network path) := by
  obtain ⟨walk, simpleWalk, rfl⟩ := (mem_graphPathSets _ _ _ path).mp membership
  have equality : pathEdgeConfiguration network walk.edges.toFinset = simplePathConfiguration network walk := by
    funext edge
    simp [pathEdgeConfiguration, simplePathConfiguration]
  rw [equality]
  exact simplePathConfiguration_minimal network simple walk simpleWalk

/-- The manuscript's bound is uniform in the actual microscopic generation.
Paths here are the actual edge sets of simple terminal walks, and `size` is
their actual number of microscopic edges. -/
theorem actual_simple_terminal_path_count (rule : Rule) (classical : rule.Classical)
    (depth size : ℕ) :
    ((graphPathSets (rule.generation depth).network.fullGraph
      (rule.generation depth).network.source (rule.generation depth).network.target).filter
        (fun path => path.card = size)).card ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  have generationSimple := (classical.generation depth).simple
  calc
    _ ≤ (minimalConfigurationsOfSize rule depth size).card := by
      apply Finset.card_le_card_of_injOn (pathEdgeConfiguration (rule.generation depth).network)
      · intro path membership
        obtain ⟨pathMembership, pathSize⟩ := Finset.mem_filter.mp membership
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, pathEdgeConfiguration_minimal _ generationSimple path pathMembership, ?_⟩
        exact (pathEdgeConfiguration_openCount _ generationSimple path pathMembership).trans pathSize
      · intro first firstMembership second secondMembership equality
        have firstImage := pathEdgeConfiguration_image (rule.generation depth).network first
          (Finset.mem_filter.mp firstMembership).1
        have secondImage := pathEdgeConfiguration_image (rule.generation depth).network second
          (Finset.mem_filter.mp secondMembership).1
        rw [equality] at firstImage
        exact firstImage.symm.trans secondImage
    _ ≤ _ := minimal_configurations_count rule classical.scale depth size

theorem actual_open_simple_terminal_path_count (rule : Rule) (classical : rule.Classical)
    (depth size : ℕ) (configuration : Configuration (rule.generation depth).edges) :
    ((graphPathSets ((rule.generation depth).network.openGraph configuration)
      (rule.generation depth).network.source (rule.generation depth).network.target).filter
        (fun path => path.card = size)).card ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  apply (Finset.card_le_card ?_).trans (actual_simple_terminal_path_count rule classical depth size)
  intro path membership
  obtain ⟨pathMembership, pathSize⟩ := Finset.mem_filter.mp membership
  obtain ⟨walk, simpleWalk, rfl⟩ := (mem_graphPathSets _ _ _ path).mp pathMembership
  apply Finset.mem_filter.mpr
  refine ⟨(mem_graphPathSets _ _ _ _).mpr ?_, pathSize⟩
  exact ⟨walk.mapLe ((rule.generation depth).network.openGraph_le_full configuration),
    simpleWalk.mapLe _, by simp⟩

/-- Fixed endpoints give a unique orientation of a simple path. Thus the
same exponential bound applies to finite families of actual walks, not only
to their edge-set representatives. -/
theorem actual_simple_terminal_walk_family_count (rule : Rule) (classical : rule.Classical)
    (depth size : ℕ)
    (walks : Finset ((rule.generation depth).network.fullGraph.Walk
      (rule.generation depth).network.source (rule.generation depth).network.target))
    (simple : ∀ walk ∈ walks, walk.IsPath) (length : ∀ walk ∈ walks, walk.length = size) :
    walks.card ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  apply (Finset.card_le_card_of_injOn (fun walk => walk.edges.toFinset) ?_ ?_).trans
    (actual_simple_terminal_path_count rule classical depth size)
  · intro walk membership
    apply Finset.mem_filter.mpr
    exact ⟨(mem_graphPathSets _ _ _ _).mpr ⟨walk, simple walk membership, rfl⟩,
      (simplePath_edgeSet_card walk (simple walk membership)).trans (length walk membership)⟩
  · intro first firstMembership second secondMembership equality
    change first.edges.toFinset = second.edges.toFinset at equality
    apply (simple second secondMembership).eq_of_edges_subset second first (simple first firstMembership)
    intro bond membership
    apply List.mem_toFinset.mp
    rw [← equality]
    exact List.mem_toFinset.mpr membership

theorem actual_simple_terminal_walk_count (rule : Rule) (classical : rule.Classical)
    (depth size : ℕ) :
    Nat.card {walk : (rule.generation depth).network.fullGraph.Walk
      (rule.generation depth).network.source (rule.generation depth).network.target //
        walk.IsPath ∧ walk.length = size} ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  let walks := (Finset.univ : Finset {walk : (rule.generation depth).network.fullGraph.Walk
    (rule.generation depth).network.source (rule.generation depth).network.target //
      walk.IsPath ∧ walk.length = size}).image Subtype.val
  have bound := actual_simple_terminal_walk_family_count rule classical depth size walks
    (by
      intro walk membership
      obtain ⟨path, _, rfl⟩ := Finset.mem_image.mp membership
      exact path.2.1)
    (by
      intro walk membership
      obtain ⟨path, _, rfl⟩ := Finset.mem_image.mp membership
      exact path.2.2)
  simpa only [walks, Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_univ, Nat.card_eq_fintype_card] using bound

end IGSIII.Chemical.Substitution
