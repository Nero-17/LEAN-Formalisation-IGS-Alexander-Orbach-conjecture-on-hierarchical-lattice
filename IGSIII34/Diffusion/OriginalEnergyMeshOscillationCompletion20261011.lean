import IGSIII34.ResistanceLimit.ElectricalNets
import IGSIII34.ResistanceLimit.SourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

/-- The actual original electrical nets control every bounded-energy
microscopic potential at all later graph depths. High-degree old vertices,
one-terminal branches and the two sides of noncrossing cells are retained. -/
theorem original_energy_uniform_net_oscillation_completion20261011
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (growth eta coefficient : ℝ) (start : ℕ)
    (growthPositive : 0 < growth) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (energyBound : ∀ depth, growth ^ (depth + 1) * sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun _ => 1) (potentials depth) ≤ bound) :
    ∀ depth age (vertex : Fin (rule.generation depth).vertices), start ≤ age + 1 →
      ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
        (rule.generation depth).network.source vertex →
      ∃ anchor ∈ finiteSkeletonVertices rule depth age,
        ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
          (rule.generation depth).network.source anchor ∧
        (potentials depth vertex - potentials depth anchor) ^ 2 ≤ coefficient * eta ^ (age + 1) * bound := by
  intro depth age vertex ageBound vertexRetained
  have mesh := finite_skeleton_is_electrical_net_of_radius_bounds rule marks growth eta coefficient start
    growthPositive etaNonnegative coefficientNonnegative radiusBound depth age [] true true vertex
    (by simpa using ageBound) vertexRetained
  obtain ⟨anchor, anchorMember, anchorRetained, close⟩ := mesh
  refine ⟨anchor, anchorMember, anchorRetained, ?_⟩
  have vertexReach : (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)).graph.Reachable
      (network (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)).source vertex := by
    rw [graph_eq_openGraph]
    exact vertexRetained
  have anchorReach : (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)).graph.Reachable
      (network (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)).source anchor := by
    rw [graph_eq_openGraph]
    change ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth [] true)).Reachable
      (rule.generation depth).network.source anchor
    simpa [plantedVertex] using anchorRetained
  have oscillation := sourceComponentEnergy_resistance_bound
    (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
    (fun _ => 1) (fun _ => zero_lt_one) (potentials depth)
    vertexReach anchorReach
  have energyNonnegative := sourceComponentEnergy_nonnegative
    (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
    (fun _ => 1) (fun _ => zero_lt_one) (potentials depth)
  have scaledEnergyNonnegative := mul_nonneg (pow_pos growthPositive (depth + 1)).le energyNonnegative
  have resistanceScaled := mul_le_mul_of_nonneg_right close scaledEnergyNonnegative
  have scaledBound := mul_le_mul_of_nonneg_left (energyBound depth)
    (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative (age + 1)))
  have cancellation :
      (pairResistance (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
        (fun _ => 1) anchor vertex / growth ^ (depth + 1)) *
      (growth ^ (depth + 1) * sourceComponentEnergy
        (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
        (fun _ => 1) (potentials depth)) =
      pairResistance (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
        (fun _ => 1) vertex anchor * sourceComponentEnergy
          (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
          (fun _ => 1) (potentials depth) := by
    rw [pairResistance_comm _ _ (fun _ => zero_lt_one) (anchorReach.symm.trans vertexReach)]
    field_simp [growthPositive.ne']
  simp only [List.length_nil, Nat.add_zero, zero_add] at resistanceScaled
  rw [cancellation] at resistanceScaled
  exact oscillation.trans (resistanceScaled.trans scaledBound)

end
end IGSIII34.Diffusion
