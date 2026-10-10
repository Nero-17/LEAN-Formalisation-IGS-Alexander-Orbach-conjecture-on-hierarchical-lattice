import IGSIII.Chemical.SmallBall.ComponentWordOwnership
import IGSIII.Chemical.SmallBall.SigmaSubtypeCoordinates
import IGSIII.Geometry.ComponentWordAnchors
import IGSIII.Geometry.AddressMetricPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem componentWordInteriorHeadTail_head (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordInterior rule marks fine (age + 1) ancestor parent) :
    (componentWordInteriorHeadTail rule marks fine age ancestor parent pair).1 = pair.1 0 := by
  change (componentWordInteriorConsEquiv rule marks fine age ancestor parent pair).1 = _
  unfold componentWordInteriorConsEquiv
  exact consSubtypeEquiv_head age _ _ _ pair

theorem componentWordInteriorHeadTail_word (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordInterior rule marks fine (age + 1) ancestor parent) :
    (componentWordInteriorHeadTail rule marks fine age ancestor parent pair).2.1 = (fun index => pair.1 index.succ) := by
  change (componentWordInteriorConsEquiv rule marks fine age ancestor parent pair).2.1 = _
  unfold componentWordInteriorConsEquiv
  exact consSubtypeEquiv_word age _ _ _ pair

theorem componentWordInteriorHeadTail_point (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordInterior rule marks fine (age + 1) ancestor parent) :
    (componentWordInteriorHeadTail rule marks fine age ancestor parent pair).2.2.val = pair.2.val := by
  change (componentWordInteriorConsEquiv rule marks fine age ancestor parent pair).2.2.val = _
  unfold componentWordInteriorConsEquiv
  exact consSubtypeEquiv_point age _ _ _ pair
def generationComponentWordEmbedding (rule : Rule) (fine : ℕ) :
    (age : ℕ) → (Fin age → Fin rule.edges) →
      (rule.generation fine).network.NetworkEmbedding (rule.generation (fine + age)).network
  | 0, _ => NetworkEmbedding.refl _
  | age + 1, word =>
      (generationComponentWordEmbedding rule fine age (fun index => word index.succ)).trans
        (rule.generationCellEmbedding (fine + age) (word 0))

theorem selectedComponentWordEmbedding_vertex (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordInterior rule marks fine age ancestor parent) :
    (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent pair).val.val =
      (generationComponentWordEmbedding rule fine age (fun index => (pair.1 index).1)).vertex pair.2.val.val := by
  induction age generalizing ancestor parent with
  | zero => rw [selectedComponentWordEmbedding]; rfl
  | succ age inductionHypothesis =>
      rw [selectedComponentWordEmbedding, generationComponentWordEmbedding]
      change (rule.generationCellEmbedding (fine + age) (pair.1 0).1).vertex
          (selectedComponentWordEmbedding rule marks crossing fine age (ancestor ++ [(pair.1 0).1])
            (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
              (marks (ancestor, parent.massOpened)) (pair.1 0).1) (pair.1 0).2)
            (componentWordInteriorHeadTail rule marks fine age ancestor parent pair).2).val.val =
        (rule.generationCellEmbedding (fine + age) (pair.1 0).1).vertex
          ((generationComponentWordEmbedding rule fine age (fun index => (pair.1 index.succ).1)).vertex pair.2.val.val)
      apply congrArg (rule.generationCellEmbedding (fine + age) (pair.1 0).1).vertex
      simpa only [componentWordInteriorHeadTail_word, componentWordInteriorHeadTail_point, componentWordInteriorHeadTail_head] using
        inductionHypothesis (ancestor ++ [(pair.1 0).1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) (pair.1 0).1) (pair.1 0).2)
          (componentWordInteriorHeadTail rule marks fine age ancestor parent pair).2

theorem generationComponentWordEmbedding_address (rule : Rule) (fine age : ℕ)
    (word : Fin age → Fin rule.edges) :
    HEq (generationComponentWordEmbedding rule fine age word)
      (generationAddressEmbedding rule (List.ofFn word) fine) := by
  induction age with
  | zero => rfl
  | succ age inductionHypothesis =>
      have addressEquality := congr_arg_heq (fun address => generationAddressEmbedding rule address fine)
        (List.ofFn_succ (f := word)).symm
      apply HEq.trans ?_ addressEquality
      change HEq
        ((generationComponentWordEmbedding rule fine age (fun index => word index.succ)).trans
          (rule.generationCellEmbedding (fine + age) (word 0)))
        ((generationAddressEmbedding rule (List.ofFn (fun index => word index.succ)) fine).trans
          (rule.generationCellEmbedding (fine + (List.ofFn (fun index => word index.succ)).length) (word 0)))
      exact dependentMap_heq
        (fun depth (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation depth).network) =>
          embedding.trans (rule.generationCellEmbedding depth (word 0)))
        (by rw [List.length_ofFn]) (inductionHypothesis (fun index => word index.succ))
theorem generationComponentWordEmbedding_zero (rule : Rule) (age : ℕ)
    (word : Fin (age + 1) → Fin rule.edges) :
    HEq (generationComponentWordEmbedding rule 0 (age + 1) word)
      (generationWordVertexEmbedding rule age word) := by
  induction age with
  | zero => rfl
  | succ age inductionHypothesis =>
      rw [generationComponentWordEmbedding, generationWordVertexEmbedding]
      exact dependentMap_heq
        (fun depth (embedding : (rule.generation 0).network.NetworkEmbedding (rule.generation depth).network) =>
          embedding.trans (rule.generationCellEmbedding depth (word 0)))
        (Nat.zero_add (age + 1)) (inductionHypothesis (fun index => word index.succ))

theorem selectedComponentWordEmbedding_address_vertex (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordInterior rule marks fine age ancestor parent) :
    HEq (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent pair).val.val
      ((generationAddressEmbedding rule (List.ofFn (fun index => (pair.1 index).1)) fine).vertex pair.2.val.val) := by
  apply HEq.trans (heq_of_eq (selectedComponentWordEmbedding_vertex rule marks crossing fine age ancestor parent pair))
  exact dependentMap_heq
    (fun depth (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation depth).network) =>
      embedding.vertex pair.2.val.val)
    (by rw [List.length_ofFn]) (generationComponentWordEmbedding_address rule fine age _)

theorem generationComponentWordEmbedding_persistent (rule : Rule) (first second : ℕ)
    (bound : first ≤ second) (age : ℕ) (word : Fin age → Fin rule.edges)
    (vertex : Fin (rule.generation first).vertices) :
    persistentVertexEmbedding rule (first + age) (second + age) (by omega)
      ((generationComponentWordEmbedding rule first age word).vertex vertex) =
      (generationComponentWordEmbedding rule second age word).vertex
        (persistentVertexEmbedding rule first second bound vertex) := by
  induction age with
  | zero => rfl
  | succ age inductionHypothesis =>
      rw [generationComponentWordEmbedding, generationComponentWordEmbedding]
      change persistentVertexEmbedding rule (first + age + 1) (second + age + 1) (by omega)
          ((rule.generationCellEmbedding (first + age) (word 0)).vertex
            ((generationComponentWordEmbedding rule first age (fun index => word index.succ)).vertex vertex)) =
        (rule.generationCellEmbedding (second + age) (word 0)).vertex
          ((generationComponentWordEmbedding rule second age (fun index => word index.succ)).vertex
            (persistentVertexEmbedding rule first second bound vertex))
      rw [generationCellEmbedding_persistent rule (first + age) (second + age) (by omega) (word 0),
        inductionHypothesis]
end
end IGSIII.Geometry