import IGSIII34.Diffusion.ActualFiniteWalk
import IGSIII34.ResistanceLimit.SourceEnergy
import IGSIII34.Percolation.Network

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII.Geometry
open scoped BigOperators

def clusterOpenRetainedEquivCompletion20261011 {vertices edges : ℕ} (rule : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    ClusterEdge rule configuration ≃ {edge : {edge : Fin edges // configuration edge = true} //
      (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1} where
  toFun edge := ⟨⟨edge.val, edge.property.1⟩, clusterEdge_first_reachable rule configuration edge⟩
  invFun edge := ⟨edge.val.val, edge.val.property, by
    have reachable := ((rule.openGraph configuration).reachableDecide_eq_true rule.source (rule.endpoint edge.val.val).1).mpr edge.property
    simp only [FiniteNetwork.active, reachable, Bool.true_or]⟩
  left_inv edge := Subtype.ext rfl
  right_inv edge := Subtype.ext (Subtype.ext rfl)

/-- The full retained cluster walk energy is exactly the source-component
unit-edge energy used for genuine original finite trace recovery. -/
theorem sourceComponentEnergy_eq_cluster_energy_completion20261011
    {vertices edges : ℕ} (rule : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (potential : Fin vertices → ℝ) :
    sourceComponentEnergy (network rule configuration) (fun _ => 1) potential =
      energy (clusterRetainedEndpoint rule configuration) (fun vertex => potential vertex.val) := by
  classical
  let response := fun edge : {edge : Fin edges // configuration edge = true} =>
    (potential (rule.endpoint edge.val).1 - potential (rule.endpoint edge.val).2) ^ 2
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
  simp only [graph_eq_openGraph, inv_one, ite_mul, one_mul, zero_mul]
  change (∑ edge : {edge : Fin edges // configuration edge = true},
    if (rule.openGraph configuration).Reachable rule.source (rule.endpoint edge.val).1 then response edge else 0) = _
  rw [filtered, ← reindexed]
  rfl

def retainedPotentialExtensionCompletion20261011 {vertices edges : ℕ} (rule : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (potential : RetainedSkeletonVertex rule configuration → ℝ) : Fin vertices → ℝ :=
  fun vertex => if retained : (rule.openGraph configuration).Reachable rule.source vertex then potential ⟨vertex, retained⟩ else 0

theorem retainedPotentialExtension_retained_completion20261011
    {vertices edges : ℕ} (rule : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (potential : RetainedSkeletonVertex rule configuration → ℝ) (vertex : RetainedSkeletonVertex rule configuration) :
    retainedPotentialExtensionCompletion20261011 rule configuration potential vertex.val = potential vertex := by
  rw [retainedPotentialExtensionCompletion20261011, dif_pos vertex.property]
  congr 1

theorem retainedPotentialExtension_energy_completion20261011
    {vertices edges : ℕ} (rule : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (potential : RetainedSkeletonVertex rule configuration → ℝ) :
    sourceComponentEnergy (network rule configuration) (fun _ => 1)
      (retainedPotentialExtensionCompletion20261011 rule configuration potential) = energy (clusterRetainedEndpoint rule configuration) potential := by
  rw [sourceComponentEnergy_eq_cluster_energy_completion20261011]
  congr 1
  funext vertex
  exact retainedPotentialExtension_retained_completion20261011 rule configuration potential vertex

end
end IGSIII34.Diffusion

