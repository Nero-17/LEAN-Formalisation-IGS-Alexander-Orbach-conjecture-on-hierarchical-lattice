import IGSIII.Chemical.PathCounting.ForestBound
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Explicit ordered forests for the first-child/next-sibling encoding. -/

set_option autoImplicit false

namespace IGSIII.Chemical.PathCounting

variable {Label : Type*}

def orderedForest : List (Label × BinaryTree Label) → BinaryTree Label
  | [] => .nil
  | entry :: rest => .node entry.1 entry.2 (orderedForest rest)

theorem orderedForest_roots (entries : List (Label × BinaryTree Label)) :
    forestRoots (orderedForest entries) = entries.length := by
  induction entries with
  | nil => simp [orderedForest, forestRoots]
  | cons entry rest inductionHypothesis => simp [orderedForest, forestRoots, inductionHypothesis, Nat.add_comm]

theorem forestLeaves_node_eq_single_add (label : Label) (children siblings : BinaryTree Label) :
    forestLeaves (.node label children siblings) =
      forestLeaves (.node label children .nil) + forestLeaves siblings := by
  cases children <;> simp [forestLeaves]

theorem orderedForest_leaves (entries : List (Label × BinaryTree Label)) :
    forestLeaves (orderedForest entries) =
      (entries.map (fun entry => forestLeaves (.node entry.1 entry.2 .nil))).sum := by
  induction entries with
  | nil => simp [orderedForest, forestLeaves]
  | cons entry rest inductionHypothesis =>
      change forestLeaves (.node entry.1 entry.2 (orderedForest rest)) =
        forestLeaves (.node entry.1 entry.2 .nil) +
          (rest.map (fun entry => forestLeaves (.node entry.1 entry.2 .nil))).sum
      rw [forestLeaves_node_eq_single_add, inductionHypothesis]

theorem orderedForest_numNodes (entries : List (Label × BinaryTree Label)) :
    (orderedForest entries).numNodes = entries.length +
      (entries.map (fun entry => entry.2.numNodes)).sum := by
  induction entries with
  | nil => simp [orderedForest]
  | cons entry rest inductionHypothesis =>
      simp only [orderedForest, BinaryTree.numNodes, inductionHypothesis,
        List.length_cons, List.map_cons, List.sum_cons]
      omega

theorem noUnaryForest_orderedForest (entries : List (Label × BinaryTree Label)) :
    noUnaryForest (orderedForest entries) ↔
      ∀ entry ∈ entries, noUnaryForest (.node entry.1 entry.2 .nil) := by
  induction entries with
  | nil => simp [orderedForest, noUnaryForest]
  | cons entry rest inductionHypothesis =>
      simp only [orderedForest, noUnaryForest, inductionHypothesis, List.mem_cons,
        forall_eq_or_imp, and_true]
      tauto

theorem orderedForest_injective : Function.Injective (orderedForest (Label := Label)) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second <;> simp_all [orderedForest]
  | cons entry rest inductionHypothesis =>
      intro second equality
      cases second with
      | nil => simp [orderedForest] at equality
      | cons secondEntry secondRest =>
          simp only [orderedForest, BinaryTree.node.injEq] at equality
          have entryEquality : entry = secondEntry := Prod.ext equality.1 equality.2.1
          have restEquality := inductionHypothesis equality.2.2
          rw [entryEquality, restEquality]

theorem noUnaryForest_single_of_children (label : Label)
    (children : List (Label × BinaryTree Label))
    (valid : ∀ entry ∈ children, noUnaryForest (.node entry.1 entry.2 .nil))
    (arity : children = [] ∨ 2 ≤ children.length) :
    noUnaryForest (.node label (orderedForest children) .nil) := by
  refine ⟨?_, (noUnaryForest_orderedForest children).mpr valid, trivial⟩
  rcases arity with empty | atLeastTwo
  · left
    rw [empty]
    rfl
  · right
    rwa [orderedForest_roots]

end IGSIII.Chemical.PathCounting
