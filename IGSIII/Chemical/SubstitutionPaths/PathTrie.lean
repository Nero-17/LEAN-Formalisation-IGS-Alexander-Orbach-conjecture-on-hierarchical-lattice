import IGSIII.Chemical.SubstitutionPaths.MinimalGeneration
import IGSIII.Chemical.PathCounting.OrderedForest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The actual used-edge address trie

The tree is extracted from the actual finest configuration through the
canonical top-down reassociation. Its edge labels are original rule-edge
indices. Empty children are removed. For a simple terminal path its finest
edge set is recovered from this encoding, and pivotal factorization prevents
unary branching at every visited cell.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Chemical.PathCounting

noncomputable def activeChildren (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) : Finset (Fin rule.edges) :=
  Finset.univ.filter fun edge => ∃ child, generationTopCells rule depth configuration edge child = true

theorem mem_activeChildren (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) (edge : Fin rule.edges) :
    edge ∈ activeChildren rule depth configuration ↔
      ∃ child, generationTopCells rule depth configuration edge child = true := by
  classical
  simp only [activeChildren, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def configurationSupportForest (rule : Rule) :
    (depth : ℕ) → Configuration (rule.generation depth).edges → BinaryTree (Option (Fin rule.edges))
  | 0, configuration => orderedForest ((openEdges configuration).toList.map fun edge => (some edge, .nil))
  | depth + 1, configuration => orderedForest ((activeChildren rule depth configuration).toList.map
      fun edge => (some edge, configurationSupportForest rule depth (generationTopCells rule depth configuration edge)))

noncomputable def configurationSupportTree (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) : BinaryTree (Option (Fin rule.edges)) :=
  .node none (configurationSupportForest rule depth configuration) .nil

theorem configurationSupportForest_roots_zero (rule : Rule)
    (configuration : Configuration rule.edges) :
    forestRoots (configurationSupportForest rule 0 configuration) = (openEdges configuration).card := by
  simp [configurationSupportForest, orderedForest_roots]

theorem configurationSupportForest_roots_succ (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) :
    forestRoots (configurationSupportForest rule (depth + 1) configuration) =
      (activeChildren rule depth configuration).card := by
  simp [configurationSupportForest, orderedForest_roots]

theorem activeChildren_empty_iff (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) :
    activeChildren rule depth configuration = ∅ ↔ configuration = fun _ => false := by
  classical
  constructor
  · intro empty
    have cellsClosed : generationTopCells rule depth configuration = fun _ _ => false := by
      funext edge child
      cases value : generationTopCells rule depth configuration edge child
      · rfl
      · have member := (mem_activeChildren rule depth configuration edge).mpr ⟨child, value⟩
        simp [empty] at member
    apply (generationTopCellsEquiv rule depth).injective
    exact cellsClosed.trans (by
      funext edge child
      rfl)
  · intro closed
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge member
    obtain ⟨child, retained⟩ := (mem_activeChildren rule depth configuration edge).mp member
    rw [generationTopCells_apply, closed] at retained
    contradiction

theorem configurationSupportForest_eq_nil_iff (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) :
    configurationSupportForest rule depth configuration = .nil ↔ configuration = fun _ => false := by
  classical
  cases depth with
  | zero =>
      simp only [configurationSupportForest]
      constructor
      · intro equality
        change orderedForest ((openEdges configuration).toList.map fun edge => (some edge, .nil)) =
          orderedForest [] at equality
        have empty := orderedForest_injective equality
        have openEmpty : openEdges configuration = ∅ := by
          simpa using empty
        funext edge
        cases value : configuration edge
        · rfl
        · have member : edge ∈ openEdges configuration := by simp [openEdges, value]
          simp [openEmpty] at member
      · intro closed
        simp [closed, openEdges, orderedForest]
  | succ depth =>
      rw [← activeChildren_empty_iff rule depth configuration]
      constructor
      · intro equality
        change orderedForest ((activeChildren rule depth configuration).toList.map fun edge =>
          (some edge, configurationSupportForest rule depth (generationTopCells rule depth configuration edge))) =
          orderedForest [] at equality
        have empty := orderedForest_injective equality
        simpa using empty
      · intro empty
        simp [configurationSupportForest, empty, orderedForest]

theorem activeChildren_eq_openEdges_root (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation (depth + 1)).network configuration) :
    activeChildren rule depth configuration = openEdges (generationRootConfiguration rule depth configuration) := by
  ext edge
  simp only [mem_activeChildren, openEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact minimal_generation_child_nonempty_iff rule depth configuration minimal edge

theorem configurationSupportForest_roots_at_least_two (rule : Rule)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (depth : ℕ) (configuration : Configuration (rule.generation depth).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation depth).network configuration) :
    2 ≤ forestRoots (configurationSupportForest rule depth configuration) := by
  cases depth with
  | zero =>
      rw [configurationSupportForest_roots_zero]
      exact crossing_two_open_edges rule.network scale configuration minimal.1
  | succ depth =>
      rw [configurationSupportForest_roots_succ, activeChildren_eq_openEdges_root rule depth configuration minimal]
      exact crossing_two_open_edges rule.network scale _ (minimal_generation_root rule depth configuration minimal).1

theorem configurationSupportTree_noUnary (rule : Rule)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    ∀ (depth : ℕ) (configuration : Configuration (rule.generation depth).edges),
      MinimalCrossingConfiguration (rule.generation depth).network configuration →
      ∀ label : Option (Fin rule.edges),
        noUnaryForest (.node label (configurationSupportForest rule depth configuration) .nil) := by
  intro depth
  induction depth with
  | zero =>
      intro configuration minimal label
      apply noUnaryForest_single_of_children
      · intro entry membership
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp membership
        simp [noUnaryForest]
      · right
        simpa only [List.length_map, Finset.length_toList] using
          crossing_two_open_edges rule.network scale configuration minimal.1
  | succ depth inductionHypothesis =>
      intro configuration minimal label
      apply noUnaryForest_single_of_children
      · intro entry membership
        obtain ⟨edge, member, rfl⟩ := List.mem_map.mp membership
        exact inductionHypothesis _
          (minimal_generation_children rule depth configuration minimal edge
            ((mem_activeChildren rule depth configuration edge).mp (Finset.mem_toList.mp member))) (some edge)
      · right
        simp only [List.length_map, Finset.length_toList]
        rw [activeChildren_eq_openEdges_root rule depth configuration minimal]
        exact crossing_two_open_edges rule.network scale _ (minimal_generation_root rule depth configuration minimal).1

end IGSIII.Chemical.Substitution
