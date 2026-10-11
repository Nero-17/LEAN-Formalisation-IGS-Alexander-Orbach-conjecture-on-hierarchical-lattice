import IGSIII34.Diffusion.ComponentEdgeOwnership
import IGSIII34.Diffusion.ActualFiniteWalk

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem componentWordEdgeConsEquiv_head (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordEdge rule marks fine (age + 1) ancestor parent) :
    (componentWordEdgeConsEquiv rule marks fine age ancestor parent pair).1 = pair.1 0 := by
  unfold componentWordEdgeConsEquiv
  exact consSubtypeEquiv_head age _ _ _ pair

theorem componentWordEdgeConsEquiv_word (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordEdge rule marks fine (age + 1) ancestor parent) :
    (componentWordEdgeConsEquiv rule marks fine age ancestor parent pair).2.1 = (fun index => pair.1 index.succ) := by
  unfold componentWordEdgeConsEquiv
  exact consSubtypeEquiv_word age _ _ _ pair

theorem componentWordEdgeConsEquiv_edge (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordEdge rule marks fine (age + 1) ancestor parent) :
    (componentWordEdgeConsEquiv rule marks fine age ancestor parent pair).2.2.val = pair.2.val := by
  unfold componentWordEdgeConsEquiv
  exact consSubtypeEquiv_point age _ _ _ pair

theorem selectedComponentWordEdgeEmbedding_edge (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (pair : ComponentWordEdge rule marks fine age ancestor parent) :
    (selectedComponentWordEdgeEmbedding rule marks crossing fine age ancestor parent pair).val =
      (generationComponentWordEmbedding rule fine age (fun index => (pair.1 index).1)).edge pair.2.val := by
  induction age generalizing ancestor parent with
  | zero => rw [selectedComponentWordEdgeEmbedding]; rfl
  | succ age inductionHypothesis =>
      rw [selectedComponentWordEdgeEmbedding, generationComponentWordEmbedding]
      change (rule.generationCellEmbedding (fine + age) (pair.1 0).1).edge
          (selectedComponentWordEdgeEmbedding rule marks crossing fine age (ancestor ++ [(pair.1 0).1])
            (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
              (marks (ancestor, parent.massOpened)) (pair.1 0).1) (pair.1 0).2)
            (componentWordEdgeConsEquiv rule marks fine age ancestor parent pair).2).val =
        (rule.generationCellEmbedding (fine + age) (pair.1 0).1).edge
          ((generationComponentWordEmbedding rule fine age (fun index => (pair.1 index.succ).1)).edge pair.2.val)
      apply congrArg (rule.generationCellEmbedding (fine + age) (pair.1 0).1).edge
      simpa only [componentWordEdgeConsEquiv_word, componentWordEdgeConsEquiv_edge,
        componentWordEdgeConsEquiv_head] using inductionHypothesis (ancestor ++ [(pair.1 0).1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) (pair.1 0).1) (pair.1 0).2)
          (componentWordEdgeConsEquiv rule marks fine age ancestor parent pair).2

theorem selectedRootWordEdgeEmbedding_bijective (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : Function.Bijective (selectedComponentWordEdgeEmbedding rule marks crossing fine age [] .connected) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨(selectedComponentWordEdgeEmbedding rule marks crossing fine age [] .connected).injective, ?_⟩
  have realCard : (Fintype.card (ComponentWordEdge rule marks fine age [] .connected) : ℝ) =
      Fintype.card (SelectedComponentEdge rule marks (fine + age) [] .connected) := by
    simp only [ComponentWordEdge, Fintype.card_sigma, Nat.cast_sum]
    simp only [selectedComponentEdge_card, List.nil_append]
    change (∑ word : Fin age → (Fin rule.edges × Bool), markedComponentEdgeMass rule marks fine (List.ofFn word)) =
      markedComponentEdgeMass rule marks (fine + age) []
    simpa only [List.nil_append] using (actual_component_edge_finite_partition rule marks crossing fine age []).symm
  exact_mod_cast realCard

def selectedRootEdgeEquiv (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) : SelectedComponentEdge rule marks depth [] .connected ≃
      ClusterEdge (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true) := by
  apply Equiv.subtypeEquivRight
  intro edge
  rw [(rule.generation depth).network.orientedChildState_connected_iff]
  simp only [OrientedState.sourceSelected, OrientedState.targetSelected, OrientedState.massOpened, decide_true]
  rw [(rule.generation depth).network.selectedActive_connected _
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)]
  simp only [selectedActive, active, Bool.true_and, Bool.false_and, Bool.or_false,
    show (LiveState.connected == LiveState.both) = false from rfl]

def actualComponentEdgeEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : ComponentWordEdge rule marks fine age [] .connected ↪
      ClusterEdge (rule.generation (fine + age)).network (markedGenerationConfiguration rule marks (fine + age) [] true) :=
  (selectedComponentWordEdgeEmbedding rule marks crossing fine age [] .connected).trans
    (selectedRootEdgeEquiv rule marks crossing (fine + age)).toEmbedding

theorem actualComponentEdgeEmbedding_surjective (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : Function.Surjective (actualComponentEdgeEmbedding rule marks crossing fine age) :=
  (selectedRootEdgeEquiv rule marks crossing (fine + age)).surjective.comp
    (selectedRootWordEdgeEmbedding_bijective rule marks crossing fine age).2

def actualComponentEdgeOwnership (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    ClusterEdge (rule.generation (fine + age)).network (markedGenerationConfiguration rule marks (fine + age) [] true) →
      Fin age → (Fin rule.edges × Bool) :=
  finiteComponentOwnership (actualComponentEdgeEmbedding rule marks crossing fine age) fallback

theorem actualComponentEdgeFrontier_empty (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : finiteComponentFrontier (actualComponentEdgeEmbedding rule marks crossing fine age) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge membership
  exact (Finset.mem_filter.mp membership).2 (actualComponentEdgeEmbedding_surjective rule marks crossing fine age edge)

theorem actualComponentEdgeOwnership_fiber_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    ((Finset.univ.filter fun edge => actualComponentEdgeOwnership rule marks crossing fine age fallback edge = word).card : ℝ) =
      markedComponentEdgeMass rule marks fine (List.ofFn word) := by
  classical
  have fiber := finiteComponentOwnership_fiber_card
    (Child := fun word : Fin age → (Fin rule.edges × Bool) => SelectedComponentEdge rule marks fine
      ([] ++ componentEdgeAddress (List.ofFn word)) (retainedComponentStateFrom rule marks [] .connected (List.ofFn word)))
    (actualComponentEdgeEmbedding rule marks crossing fine age) fallback word
  have realFiber := congrArg (fun count : ℕ => (count : ℝ)) fiber
  simpa only [actualComponentEdgeOwnership, actualComponentEdgeFrontier_empty, Finset.card_empty,
    ite_self, Nat.add_zero, selectedComponentEdge_card, List.nil_append, markedComponentEdgeMass,
    retainedComponentState] using realFiber

end
end IGSIII34.Diffusion
