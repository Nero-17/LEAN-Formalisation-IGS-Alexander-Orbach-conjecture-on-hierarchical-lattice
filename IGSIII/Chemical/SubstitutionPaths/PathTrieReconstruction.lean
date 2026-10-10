import IGSIII.Chemical.SubstitutionPaths.PathTrie

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Chemical.PathCounting

theorem orderedForest_matching_entry {edges : ℕ}
    (first second : Finset (Fin edges))
    (firstChildren secondChildren : Fin edges → BinaryTree (Option (Fin edges)))
    (equality : orderedForest (first.toList.map fun edge => (some edge, firstChildren edge)) =
      orderedForest (second.toList.map fun edge => (some edge, secondChildren edge)))
    (edge : Fin edges) (membership : edge ∈ first) :
    edge ∈ second ∧ firstChildren edge = secondChildren edge := by
  have lists := orderedForest_injective equality
  have entry : (some edge, firstChildren edge) ∈
      first.toList.map (fun other => (some other, firstChildren other)) :=
    List.mem_map.mpr ⟨edge, Finset.mem_toList.mpr membership, rfl⟩
  rw [lists] at entry
  obtain ⟨other, otherMembership, pairEquality⟩ := List.mem_map.mp entry
  have same : other = edge := Option.some.inj (congrArg Prod.fst pairEquality)
  subst other
  exact ⟨Finset.mem_toList.mp otherMembership, (congrArg Prod.snd pairEquality).symm⟩

theorem configurationSupportForest_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (configurationSupportForest rule depth) := by
  classical
  induction depth with
  | zero =>
      intro first second equality
      funext edge
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro retained
        have member : edge ∈ openEdges first := by simp [openEdges, retained]
        have matching := orderedForest_matching_entry (openEdges first) (openEdges second)
          (fun _ => .nil) (fun _ => .nil) equality edge member
        exact (Finset.mem_filter.mp matching.1).2
      · intro retained
        have member : edge ∈ openEdges second := by simp [openEdges, retained]
        have matching := orderedForest_matching_entry (openEdges second) (openEdges first)
          (fun _ => .nil) (fun _ => .nil) equality.symm edge member
        exact (Finset.mem_filter.mp matching.1).2
  | succ depth inductionHypothesis =>
      intro first second equality
      apply (generationTopCellsEquiv rule depth).injective
      funext edge
      by_cases nonempty : ∃ child, generationTopCells rule depth first edge child = true
      · have matching := orderedForest_matching_entry (activeChildren rule depth first)
          (activeChildren rule depth second)
          (fun edge => configurationSupportForest rule depth (generationTopCells rule depth first edge))
          (fun edge => configurationSupportForest rule depth (generationTopCells rule depth second edge))
          equality edge ((mem_activeChildren rule depth first edge).mpr nonempty)
        exact inductionHypothesis matching.2
      · have secondEmpty : ¬ ∃ child, generationTopCells rule depth second edge child = true := by
          intro secondNonempty
          have matching := orderedForest_matching_entry (activeChildren rule depth second)
            (activeChildren rule depth first)
            (fun edge => configurationSupportForest rule depth (generationTopCells rule depth second edge))
            (fun edge => configurationSupportForest rule depth (generationTopCells rule depth first edge))
            equality.symm edge ((mem_activeChildren rule depth second edge).mpr secondNonempty)
          exact nonempty ((mem_activeChildren rule depth first edge).mp matching.1)
        funext child
        change generationTopCells rule depth first edge child = generationTopCells rule depth second edge child
        cases firstValue : generationTopCells rule depth first edge child <;>
          cases secondValue : generationTopCells rule depth second edge child
        · rfl
        · exact False.elim (secondEmpty ⟨child, secondValue⟩)
        · exact False.elim (nonempty ⟨child, firstValue⟩)
        · rfl

theorem configurationSupportTree_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (configurationSupportTree rule depth) := by
  intro first second equality
  apply configurationSupportForest_injective rule depth
  exact (BinaryTree.node.inj equality).2.1

theorem forestLeaves_single_nonempty {Label : Type*} (label : Label) (children : BinaryTree Label)
    (nonempty : children ≠ .nil) :
    forestLeaves (.node label children .nil) = forestLeaves children := by
  cases children with
  | nil => contradiction
  | node childLabel firstChild siblings => simp [forestLeaves]

theorem openCount_eq_zero_iff {edges : ℕ} (configuration : Configuration edges) :
    openCount configuration = 0 ↔ configuration = fun _ => false := by
  classical
  constructor
  · intro zero
    have empty : openEdges configuration = ∅ := Finset.card_eq_zero.mp zero
    funext edge
    cases value : configuration edge
    · rfl
    · have member : edge ∈ openEdges configuration := by simp [openEdges, value]
      simp [empty] at member
  · intro empty
    simp [openCount, empty]

theorem configurationSupportForest_leaves (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) :
    forestLeaves (configurationSupportForest rule depth configuration) = openCount configuration := by
  classical
  induction depth with
  | zero =>
      simp [configurationSupportForest, orderedForest_leaves, List.map_map, forestLeaves,
        ← openEdges_card]
  | succ depth inductionHypothesis =>
      rw [configurationSupportForest, orderedForest_leaves, List.map_map]
      simp only [Function.comp_def]
      have each : ∀ edge ∈ (activeChildren rule depth configuration).toList,
          forestLeaves (.node (some edge)
            (configurationSupportForest rule depth (generationTopCells rule depth configuration edge)) .nil) =
          openCount (generationTopCells rule depth configuration edge) := by
        intro edge membership
        have nonempty := (mem_activeChildren rule depth configuration edge).mp (Finset.mem_toList.mp membership)
        have forestNonempty : configurationSupportForest rule depth
            (generationTopCells rule depth configuration edge) ≠ .nil := by
          intro empty
          have closed := (configurationSupportForest_eq_nil_iff rule depth _).mp empty
          obtain ⟨child, retained⟩ := nonempty
          rw [closed] at retained
          contradiction
        rw [forestLeaves_single_nonempty _ _ forestNonempty, inductionHypothesis]
      rw [List.map_congr_left each, Finset.sum_map_toList]
      rw [generation_openCount_topCells]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro edge _ notActive
      apply (openCount_eq_zero_iff _).mpr
      funext child
      cases value : generationTopCells rule depth configuration edge child
      · rfl
      · exact False.elim (notActive ((mem_activeChildren rule depth configuration edge).mpr ⟨child, value⟩))

theorem configurationSupportTree_leaves (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges)
    (nonempty : ∃ edge, configuration edge = true) :
    forestLeaves (configurationSupportTree rule depth configuration) = openCount configuration := by
  have forestNonempty : configurationSupportForest rule depth configuration ≠ .nil := by
    intro empty
    have closed := (configurationSupportForest_eq_nil_iff rule depth configuration).mp empty
    obtain ⟨edge, retained⟩ := nonempty
    rw [closed] at retained
    contradiction
  exact (forestLeaves_single_nonempty none _ forestNonempty).trans
    (configurationSupportForest_leaves rule depth configuration)

theorem minimal_configuration_nonempty {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (minimal : MinimalCrossingConfiguration network configuration) :
    ∃ edge, configuration edge = true := by
  by_contra empty
  have closed : configuration = fun _ => false := by
    funext edge
    cases value : configuration edge
    · rfl
    · exact False.elim (empty ⟨edge, value⟩)
  have crossing := minimal.1
  rw [closed, network.crosses_all_closed] at crossing
  contradiction

theorem configurationSupportTree_node_bound (rule : Rule)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (depth : ℕ) (configuration : Configuration (rule.generation depth).edges)
    (minimal : MinimalCrossingConfiguration (rule.generation depth).network configuration) :
    (configurationSupportTree rule depth configuration).numNodes ≤ 2 * openCount configuration - 1 := by
  have bound := singleTree_node_count_le_twice_leaves_sub_one none
    (configurationSupportForest rule depth configuration)
    (configurationSupportTree_noUnary rule scale depth configuration minimal none)
  rw [← configurationSupportTree, configurationSupportTree_leaves rule depth configuration
    (minimal_configuration_nonempty _ _ minimal)] at bound
  exact bound

end IGSIII.Chemical.Substitution
