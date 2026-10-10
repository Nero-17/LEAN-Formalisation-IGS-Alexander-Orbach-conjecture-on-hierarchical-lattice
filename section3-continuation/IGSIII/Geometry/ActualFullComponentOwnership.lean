import IGSIII.Geometry.ActualFiniteMass
import IGSIII.Geometry.FiniteUniformOwnership
import IGSIII.Chemical.SmallBall.ComponentWordOwnership
import IGSIII.Mass.FullComponentEmpiricalWeights

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory ProbabilityTheory Classical Filter
open scoped BigOperators Topology

def actualComponentVertexEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) :
    ComponentWordInterior rule marks fine age [] .connected ↪
      ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + age) :=
  (selectedComponentWordEmbedding rule marks crossing fine age [] .connected).trans
    (selectedRootInteriorEmbedding rule marks crossing scale scalePositive (fine + age))

def actualComponentVertexOwnership (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + age) →
      Fin age → (Fin rule.edges × Bool) :=
  finiteComponentOwnership (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age) fallback

def actualComponentVertexFrontier (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) :
    Finset (ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + age)) :=
  finiteComponentFrontier (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age)

theorem actualComponentVertexFrontier_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) :
    ((actualComponentVertexFrontier rule marks crossing scale scalePositive fine age).card : ℝ) =
      componentFrontierVertexMass rule marks age [] + 2 := by
  have partition := finiteComponentFrontier_card_partition
    (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age)
  have realPartition := congrArg (fun count : ℕ => (count : ℝ)) partition
  simp only [Nat.cast_add, Nat.cast_sum, selectedComponentInterior_card] at realPartition
  rw [← Nat.card_eq_fintype_card, actualFiniteCluster_card rule marks crossing] at realPartition
  have actualPartition := actual_component_finite_partition rule marks crossing fine age []
  simp only [markedComponentVertexMass, retainedComponentState, retainedComponentStateFrom,
    componentEdgeAddress, List.map_nil, List.nil_append] at actualPartition
  simp only [List.nil_append, componentEdgeAddress] at realPartition
  change ((finiteComponentFrontier (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age)).card : ℝ) = _
  change markedOrientedVertexMass rule marks (fine + age) [] .connected = _ at actualPartition
  change markedOrientedVertexMass rule marks (fine + age) [] .connected + 2 = _ at realPartition
  linarith

theorem actualComponentVertexOwnership_law (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + age)).map
        (actualComponentVertexOwnership rule marks crossing scale scalePositive fine age fallback) =
      fullComponentEmpiricalWordLaw rule marks crossing fine age fallback := by
  apply Measure.ext_of_singleton
  intro word
  rw [fullComponentEmpiricalWordLaw, finiteWeightPMF_singleton]
  change (uniformOn (Set.univ : Set (ActualFiniteCluster rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + age)))).map
      (finiteComponentOwnership (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age) fallback) {word} = _
  rw [finite_uniform_ownership_singleton]
  congr 1
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero, selectedComponentInterior_card,
    List.nil_append]
  rw [← Nat.card_eq_fintype_card, actualFiniteCluster_card rule marks crossing]
  have frontierCard : ((finiteComponentFrontier
      (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age)).card : ℝ) =
      componentFrontierVertexMass rule marks age [] + 2 :=
    actualComponentVertexFrontier_card rule marks crossing scale scalePositive fine age
  rw [frontierCard]
  rfl

theorem actualComponentVertexOwnership_nonfrontier (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (point : ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + age))
    (nonfrontier : point ∉ actualComponentVertexFrontier rule marks crossing scale scalePositive fine age) :
    ∃ child : SelectedComponentInterior rule marks fine
        (componentEdgeAddress (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine age fallback point)))
        (retainedComponentState rule marks (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine age fallback point))),
      actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age
        ⟨actualComponentVertexOwnership rule marks crossing scale scalePositive fine age fallback point, child⟩ = point := by
  obtain ⟨child, equality⟩ := finiteComponentOwnership_inside
    (actualComponentVertexEmbedding rule marks crossing scale scalePositive fine age) fallback point nonfrontier
  refine ⟨child, ?_⟩
  exact equality

theorem actualComponentVertexFrontier_mass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ) :
    actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + age) (actualComponentVertexFrontier rule marks crossing scale scalePositive fine age) =
      ENNReal.ofReal ((componentFrontierVertexMass rule marks age [] + 2) /
        (markedComponentVertexMass rule marks (fine + age) [] + 2)) := by
  rw [actualFiniteClusterMeasure, uniformOn_univ_finset, actualComponentVertexFrontier_card,
    ← Nat.card_eq_fintype_card, actualFiniteCluster_card rule marks crossing]

end
end IGSIII.Geometry
