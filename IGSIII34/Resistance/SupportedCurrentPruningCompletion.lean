import IGSIII34.Resistance.Minimizer
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open Function
variable {Vertex Edge OtherEdge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [Fintype OtherEdge] [DecidableEq OtherEdge]

theorem supported_current_divergence_restriction_completion
    (network : FiniteNetwork Vertex Edge) (retained : FiniteNetwork Vertex OtherEdge)
    (inclusion : OtherEdge → Edge) (injective : Function.Injective inclusion)
    (endpoint : ∀ edge, retained.endpoint edge = network.endpoint (inclusion edge))
    (current : Edge → ℝ) (supported : ∀ edge ∉ Set.range inclusion, current edge = 0) (vertex : Vertex) :
    retained.divergence (fun edge => current (inclusion edge)) vertex = network.divergence current vertex := by
  unfold divergence
  exact Fintype.sum_of_injective inclusion injective _ _
    (fun edge outside => by rw [supported edge outside, zero_mul])
    (fun edge => by rw [endpoint edge])

theorem supported_current_energy_restriction_completion
    (inclusion : OtherEdge → Edge) (injective : Function.Injective inclusion)
    (resistance current : Edge → ℝ) (supported : ∀ edge ∉ Set.range inclusion, current edge = 0) :
    energy (fun edge => resistance (inclusion edge)) (fun edge => current (inclusion edge)) = energy resistance current := by
  unfold energy
  exact Fintype.sum_of_injective inclusion injective _ _
    (fun edge outside => by rw [supported edge outside]; simp)
    (fun _ => rfl)

/-- Deleting any collection of edges carrying zero minimizing current
preserves the exact Thomson resistance. No resistance preservation is an
input hypothesis. -/
theorem effectiveResistance_supported_current_pruning_completion
    (network : FiniteNetwork Vertex Edge) (retained : FiniteNetwork Vertex OtherEdge)
    (inclusion : OtherEdge → Edge) (injective : Function.Injective inclusion)
    (endpoint : ∀ edge, retained.endpoint edge = network.endpoint (inclusion edge))
    (source : retained.source = network.source) (target : retained.target = network.target)
    (resistance current : Edge → ℝ) (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (unitFlow : current ∈ network.unitFlows) (minimal : energy resistance current = network.effectiveResistance resistance)
    (supported : ∀ edge ∉ Set.range inclusion, current edge = 0) :
    retained.effectiveResistance (fun edge => resistance (inclusion edge)) = network.effectiveResistance resistance := by
  classical
  have retainedFlow : (fun edge => current (inclusion edge)) ∈ retained.unitFlows := by
    intro vertex
    rw [supported_current_divergence_restriction_completion network retained inclusion injective endpoint current supported]
    simpa only [source, target] using unitFlow vertex
  apply le_antisymm
  · have bound := retained.effectiveResistance_le_energy (fun edge => nonnegative (inclusion edge)) retainedFlow
    rwa [supported_current_energy_restriction_completion inclusion injective resistance current supported, minimal] at bound
  · apply retained.le_effectiveResistance ⟨_, retainedFlow⟩
    intro competitor competitorFlow
    let extension : Edge → ℝ := inclusion.extend competitor (fun _ => 0)
    have outside : ∀ edge ∉ Set.range inclusion, extension edge = 0 := by
      intro edge outside
      exact Function.extend_apply' _ _ edge (by simpa only [Set.mem_range] using outside)
    have inside : ∀ edge, extension (inclusion edge) = competitor edge := fun edge => injective.extend_apply _ _ edge
    have extendedFlow : extension ∈ network.unitFlows := by
      intro vertex
      rw [← supported_current_divergence_restriction_completion network retained inclusion injective endpoint extension outside]
      simp_rw [inside]
      simpa only [source, target] using competitorFlow vertex
    have bound := network.effectiveResistance_le_energy nonnegative extendedFlow
    have energyIdentity := supported_current_energy_restriction_completion inclusion injective resistance extension outside
    simp_rw [inside] at energyIdentity
    rwa [← energyIdentity] at bound

end
end IGSIII34.Resistance.FiniteNetwork
