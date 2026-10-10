import IGSIII.Chemical.PathCounting.BinaryCode

/-! Node bounds for first-child/next-sibling encodings with no unary branching.
Here a node's left child encodes its entire child forest and its right child
encodes its next siblings. These definitions do not assert a graph encoding. -/

set_option autoImplicit false

namespace IGSIII.Chemical.PathCounting

variable {Label : Type*}

def forestRoots : BinaryTree Label → ℕ
  | .nil => 0
  | .node _ _ right => 1 + forestRoots right

def forestLeaves : BinaryTree Label → ℕ
  | .nil => 0
  | .node _ .nil right => 1 + forestLeaves right
  | .node _ (.node label left right) siblings =>
      forestLeaves (.node label left right) + forestLeaves siblings

def noUnaryForest : BinaryTree Label → Prop
  | .nil => True
  | .node _ left right =>
      (left = .nil ∨ 2 ≤ forestRoots left) ∧ noUnaryForest left ∧ noUnaryForest right

theorem noUnaryForest_node_count (tree : BinaryTree Label) (valid : noUnaryForest tree) :
    tree.numNodes + forestRoots tree ≤ 2 * forestLeaves tree := by
  induction tree with
  | nil => simp [forestRoots, forestLeaves]
  | node label left right leftInduction rightInduction =>
      have leftBound := leftInduction valid.2.1
      have rightBound := rightInduction valid.2.2
      cases left with
      | nil =>
          simp only [BinaryTree.numNodes, forestRoots, forestLeaves] at *
          omega
      | node childLabel firstChild nextChild =>
          have twoChildren : 2 ≤ forestRoots (.node childLabel firstChild nextChild) :=
            valid.1.resolve_left (by simp)
          simp only [BinaryTree.numNodes, forestRoots, forestLeaves] at *
          omega

theorem singleTree_node_count_le_twice_leaves_sub_one
    (label : Label) (children : BinaryTree Label)
    (valid : noUnaryForest (.node label children .nil)) :
    (BinaryTree.node label children .nil).numNodes ≤
      2 * forestLeaves (.node label children .nil) - 1 := by
  have bound := noUnaryForest_node_count (.node label children .nil) valid
  simp only [forestRoots] at bound
  omega

theorem singleTree_leaves_positive (label : Label) (children : BinaryTree Label)
    (valid : noUnaryForest (.node label children .nil)) :
    0 < forestLeaves (.node label children .nil) := by
  have bound := noUnaryForest_node_count (.node label children .nil) valid
  simp only [forestRoots, BinaryTree.numNodes] at bound
  omega

end IGSIII.Chemical.PathCounting
