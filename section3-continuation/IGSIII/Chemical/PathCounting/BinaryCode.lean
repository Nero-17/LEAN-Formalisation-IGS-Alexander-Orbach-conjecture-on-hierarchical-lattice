import Mathlib.Data.Tree.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A finite alphabet bound for labelled binary encodings of hierarchical paths.
The graph-to-tree injection is a separate combinatorial obligation. -/

set_option autoImplicit false

namespace IGSIII.Chemical.PathCounting

open scoped BigOperators

variable {Label : Type*}

def binaryPrefixCode : BinaryTree Label → List (Option Label)
  | .nil => [none]
  | .node label left right => some label :: (binaryPrefixCode left ++ binaryPrefixCode right)

theorem binaryPrefixCode_length (tree : BinaryTree Label) :
    (binaryPrefixCode tree).length = 2 * tree.numNodes + 1 := by
  induction tree with
  | nil => simp [binaryPrefixCode]
  | node label left right leftInduction rightInduction =>
      simp only [binaryPrefixCode, List.length_cons, List.length_append,
        leftInduction, rightInduction, BinaryTree.numNodes]
      omega

theorem binaryPrefixCode_prefix_unique (first : BinaryTree Label) :
    ∀ (second : BinaryTree Label) (firstTail secondTail : List (Option Label)),
      binaryPrefixCode first ++ firstTail = binaryPrefixCode second ++ secondTail →
        first = second ∧ firstTail = secondTail := by
  induction first with
  | nil =>
      intro second firstTail secondTail equality
      cases second with
      | nil => simpa only [binaryPrefixCode, List.singleton_append, List.cons.injEq, true_and] using equality
      | node label left right => simp [binaryPrefixCode] at equality
  | node label left right leftInduction rightInduction =>
      intro second firstTail secondTail equality
      cases second with
      | nil => simp [binaryPrefixCode] at equality
      | node secondLabel secondLeft secondRight =>
          simp only [binaryPrefixCode, List.cons_append, List.cons.injEq, Option.some.injEq,
            List.append_assoc] at equality
          obtain ⟨leftEquality, remainderEquality⟩ :=
            leftInduction secondLeft (binaryPrefixCode right ++ firstTail)
              (binaryPrefixCode secondRight ++ secondTail) equality.2
          obtain ⟨rightEquality, tailEquality⟩ :=
            rightInduction secondRight firstTail secondTail remainderEquality
          exact ⟨by rw [equality.1, leftEquality, rightEquality], tailEquality⟩

theorem binaryPrefixCode_injective : Function.Injective (binaryPrefixCode (Label := Label)) := by
  intro first second equality
  exact (binaryPrefixCode_prefix_unique first second [] [] (by simpa using equality)).1

variable [Fintype Label] [DecidableEq Label]

def boundedWords : ℕ → Finset (List Label)
  | 0 => {[]}
  | depth + 1 => insert [] (Finset.univ.biUnion fun label => (boundedWords depth).image (List.cons label))

theorem mem_boundedWords (word : List Label) (bound : ℕ) :
    word ∈ boundedWords bound ↔ word.length ≤ bound := by
  induction bound generalizing word with
  | zero => simp [boundedWords]
  | succ bound inductionHypothesis =>
      cases word with
      | nil => simp [boundedWords]
      | cons label tail =>
          simp only [boundedWords, Finset.mem_insert, List.cons_ne_nil, false_or,
            Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · rintro ⟨first, rest, restMember, equality⟩
            have restEqual := (List.cons.inj equality).2
            have restBound := (inductionHypothesis rest).mp restMember
            simpa only [restEqual, List.length_cons, Nat.add_le_add_iff_right] using
              Nat.add_le_add_right restBound 1
          · intro lengthBound
            refine ⟨label, tail, (inductionHypothesis tail).mpr ?_, rfl⟩
            simpa using lengthBound

theorem boundedWords_card_le (bound : ℕ) :
    (boundedWords (Label := Label) bound).card ≤ (Fintype.card Label + 1) ^ bound := by
  induction bound with
  | zero => simp [boundedWords]
  | succ bound inductionHypothesis =>
      have unionBound :
          (Finset.univ.biUnion fun label : Label =>
            (boundedWords bound).image (List.cons label)).card ≤
              Fintype.card Label * (boundedWords (Label := Label) bound).card := by
        calc
          _ ≤ ∑ label : Label, ((boundedWords bound).image (List.cons label)).card := Finset.card_biUnion_le
          _ ≤ ∑ _label : Label, (boundedWords (Label := Label) bound).card :=
            Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
          _ = _ := by simp
      have oneBound : 1 ≤ (Fintype.card Label + 1) ^ bound := one_le_pow₀ (by omega)
      calc
        _ ≤ (Finset.univ.biUnion fun label : Label =>
            (boundedWords bound).image (List.cons label)).card + 1 := Finset.card_insert_le _ _
        _ ≤ Fintype.card Label * (boundedWords (Label := Label) bound).card + 1 := Nat.add_le_add_right unionBound 1
        _ ≤ Fintype.card Label * (Fintype.card Label + 1) ^ bound + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ inductionHypothesis) 1
        _ ≤ (Fintype.card Label + 1) ^ (bound + 1) := by
          rw [pow_succ]
          nlinarith

theorem binaryTree_family_card_le_words (trees : Finset (BinaryTree Label)) (nodeBound : ℕ)
    (bounded : ∀ tree ∈ trees, tree.numNodes ≤ nodeBound) :
    trees.card ≤ (Fintype.card Label + 2) ^ (2 * nodeBound + 1) := by
  calc
    _ ≤ (boundedWords (Label := Option Label) (2 * nodeBound + 1)).card := by
      apply Finset.card_le_card_of_injOn binaryPrefixCode
      · intro tree membership
        apply (mem_boundedWords _ _).mpr
        rw [binaryPrefixCode_length]
        have := bounded tree membership
        omega
      · intro first _ second _ equality
        exact binaryPrefixCode_injective equality
    _ ≤ _ := by simpa [Fintype.card_option, Nat.add_assoc] using
      boundedWords_card_le (Label := Option Label) (2 * nodeBound + 1)

theorem binaryTree_family_card_le_exponential (trees : Finset (BinaryTree Label))
    {leaves : ℕ} (leavesPositive : 0 < leaves)
    (bounded : ∀ tree ∈ trees, tree.numNodes ≤ 2 * leaves - 1) :
    trees.card ≤ ((Fintype.card Label + 2) ^ 4) ^ leaves := by
  calc
    _ ≤ (Fintype.card Label + 2) ^ (2 * (2 * leaves - 1) + 1) :=
      binaryTree_family_card_le_words trees _ bounded
    _ ≤ (Fintype.card Label + 2) ^ (4 * leaves) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    _ = _ := by rw [pow_mul]

end IGSIII.Chemical.PathCounting
