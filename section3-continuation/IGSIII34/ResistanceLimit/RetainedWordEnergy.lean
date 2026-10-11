import IGSIII34.Diffusion.ExactEdgeOwnership
import IGSIII34.Diffusion.ClusterSourceEnergyCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

/-- Arbitrary positive or signed edge weights can be restricted exactly to
the retained cluster; no terminal-only reduction occurs in this identity. -/
theorem sourceComponentEnergy_eq_weighted_cluster_energy
    {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ)
    (potential : Fin vertices → ℝ) :
    sourceComponentEnergy (network rule configuration) resistance potential =
      ∑ edge : ClusterEdge rule configuration,
        (resistance ⟨edge.val, edge.property.1⟩)⁻¹ *
          (potential (rule.endpoint edge.val).1 - potential (rule.endpoint edge.val).2) ^ 2 := by
  classical
  let response := fun edge : {edge : Fin edges // configuration edge = true} =>
    (resistance edge)⁻¹ * (potential (rule.endpoint edge.val).1 - potential (rule.endpoint edge.val).2) ^ 2
  have filtered :
      (∑ edge : {edge : Fin edges // configuration edge = true},
        if (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1 then response edge else 0) =
      ∑ edge : {edge : {edge : Fin edges // configuration edge = true} //
        (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1}, response edge.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun edge : {edge : Fin edges // configuration edge = true} =>
      (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1)
      (by simp) response
  have reindexed := (clusterOpenRetainedEquivCompletion20261011 rule configuration).sum_comp
    (fun edge => response edge.val)
  unfold sourceComponentEnergy finiteEnergy
  simp only [graph_eq_openGraph, ite_mul, zero_mul]
  change (∑ edge : {edge : Fin edges // configuration edge = true},
    if (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1 then response edge else 0) = _
  rw [filtered, ← reindexed]
  rfl

/-- The energy of an actual retained word is the sum over precisely its
selected descendant edges. The two sides of a B socket are separate words. -/
def retainedWordTraceEnergy (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ)
    (resistance : {edge : Fin (rule.generation (fine + age)).edges //
      markedGenerationConfiguration rule marks (fine + age) [] true edge = true} → ℝ)
    (potential : Fin (rule.generation (fine + age)).vertices → ℝ)
    (word : Fin age → (Fin rule.edges × Bool)) : ℝ :=
  ∑ edge : SelectedComponentEdge rule marks fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks (List.ofFn word)),
    let physical := actualComponentEdgeEmbedding rule marks crossing fine age ⟨word, edge⟩
    (resistance ⟨physical.val, physical.property.1⟩)⁻¹ *
      (potential ((rule.generation (fine + age)).network.endpoint physical.val).1 -
        potential ((rule.generation (fine + age)).network.endpoint physical.val).2) ^ 2

theorem sourceComponentEnergy_eq_sum_retained_word_energy
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ)
    (resistance : {edge : Fin (rule.generation (fine + age)).edges //
      markedGenerationConfiguration rule marks (fine + age) [] true edge = true} → ℝ)
    (potential : Fin (rule.generation (fine + age)).vertices → ℝ) :
    sourceComponentEnergy (network (rule.generation (fine + age)).network
      (markedGenerationConfiguration rule marks (fine + age) [] true)) resistance potential =
      ∑ word : Fin age → (Fin rule.edges × Bool),
        retainedWordTraceEnergy rule marks crossing fine age resistance potential word := by
  classical
  rw [sourceComponentEnergy_eq_weighted_cluster_energy]
  let equivalence := Equiv.ofBijective (actualComponentEdgeEmbedding rule marks crossing fine age)
    ⟨(actualComponentEdgeEmbedding rule marks crossing fine age).injective,
      actualComponentEdgeEmbedding_surjective rule marks crossing fine age⟩
  rw [← equivalence.sum_comp]
  change (∑ pair : ComponentWordEdge rule marks fine age [] .connected, _) = _
  erw [Fintype.sum_sigma]
  rfl

theorem retainedWordTraceEnergy_nonnegative
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ)
    (resistance : {edge : Fin (rule.generation (fine + age)).edges //
      markedGenerationConfiguration rule marks (fine + age) [] true edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : Fin (rule.generation (fine + age)).vertices → ℝ)
    (word : Fin age → (Fin rule.edges × Bool)) :
    0 ≤ retainedWordTraceEnergy rule marks crossing fine age resistance potential word := by
  apply Finset.sum_nonneg
  intro edge _
  exact mul_nonneg (inv_pos.mpr (positive _)).le (sq_nonneg _)

end
end IGSIII34.ResistanceLimit
