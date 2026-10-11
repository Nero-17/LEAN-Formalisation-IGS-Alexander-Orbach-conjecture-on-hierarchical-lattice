import IGSIII34.ResistanceLimit.SelectedComponentEnergy
import IGSIII34.ResistanceLimit.StationarySideGeneration

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution

theorem stationary_selectedComponentTraceEnergy_monotone
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (word : List (Fin rule.edges × Bool))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (restriction : ∀ depth vertex, potentials (depth + 1) (rule.generationOldVertex depth vertex) = potentials depth vertex) :
    Monotone (fun depth => selectedComponentTraceEnergy rule marks depth word
      (fun edge => stationaryGenerationResistance rule field growth depth (componentEdgeAddress word) edge.val)
      (potentials depth)) := by
  by_cases inactive : retainedComponentState rule marks word = .inactive
  · simp only [selectedComponentTraceEnergy, if_pos inactive]
    exact monotone_const
  · apply monotone_nat_of_le_succ
    intro depth
    simp only [selectedComponentTraceEnergy, if_neg inactive]
    have comparison := stationary_generation_side_source_energy_le rule marks field growth growthPositive
      fieldPositive crossing stationary depth (componentEdgeAddress word)
      (retainedComponentState rule marks word).massOpened
      (retainedComponentState rule marks word).sourceSelected (potentials (depth + 1))
    simpa only [restriction] using comparison

end
end IGSIII34.ResistanceLimit
