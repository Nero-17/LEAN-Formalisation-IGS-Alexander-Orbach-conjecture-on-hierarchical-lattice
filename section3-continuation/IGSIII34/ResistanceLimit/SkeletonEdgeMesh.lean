import IGSIII34.ResistanceLimit.SkeletonEnergy
import IGSIII34.Resistance.FlowPaths

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem pairResistance_endpoint_le {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (nonnegative : ∀ edge, 0 ≤ resistance edge) (edge : Edge) :
    pairResistance network resistance (network.endpoint edge).1 (network.endpoint edge).2 ≤ resistance edge := by
  by_cases distinct : (network.endpoint edge).1 ≠ (network.endpoint edge).2
  · rw [pairResistance, dif_pos distinct]
    have unitFlow : (fun index => if index = edge then (1 : ℝ) else 0) ∈
        (retarget network (network.endpoint edge).1 (network.endpoint edge).2 distinct).unitFlows := by
      intro vertex
      rw [divergence_single]
      rfl
    have bound := (retarget network (network.endpoint edge).1 (network.endpoint edge).2 distinct).effectiveResistance_le_energy
      nonnegative unitFlow
    simpa [Resistance.FiniteNetwork.energy] using bound
  · rw [not_ne_iff.mp distinct, pairResistance_self]
    exact nonnegative edge

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem skeletonEnergyEndpoint_distance_le_resistance (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // configuration depth edge = true})
    (nonzero : skeletonEnergyConductance rule configuration resistance depth edge ≠ 0) :
    dist (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible depth edge).1
      (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible depth edge).2 ≤
        resistance depth edge := by
  have firstRetained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1 := by
    by_contra absent
    exact nonzero (by simp only [skeletonEnergyConductance, if_neg absent])
  have adjacent : ((rule.generation depth).network.openGraph (configuration depth)).Adj
      ((rule.generation depth).network.endpoint edge.val).1 ((rule.generation depth).network.endpoint edge.val).2 :=
    ⟨(rule.generation depth).network.loopless edge.val, edge.val, edge.property, Or.inl rfl⟩
  have lastRetained := firstRetained.trans adjacent.reachable
  change dist (electricalSkeletonPoint rule configuration coherent resistance positive compatible depth
    ((rule.generation depth).network.endpoint edge.val).1)
    (electricalSkeletonPoint rule configuration coherent resistance positive compatible depth
      ((rule.generation depth).network.endpoint edge.val).2) ≤ _
  rw [electricalSkeletonPoint_retained rule configuration coherent resistance positive compatible depth
      ⟨_, firstRetained⟩,
    electricalSkeletonPoint_retained rule configuration coherent resistance positive compatible depth
      ⟨_, lastRetained⟩, electricalSkeletonVertex_distance]
  exact pairResistance_endpoint_le (network (rule.generation depth).network (configuration depth))
    (resistance depth) (fun edge => (positive depth edge).le) edge

end
end IGSIII34.ResistanceLimit
