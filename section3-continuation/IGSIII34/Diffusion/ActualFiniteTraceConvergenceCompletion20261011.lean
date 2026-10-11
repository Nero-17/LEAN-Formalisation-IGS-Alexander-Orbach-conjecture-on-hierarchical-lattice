import IGSIII34.ResistanceLimit.ActualSkeletonLimit
import IGSIII34.ResistanceLimit.SourceActualTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open Resistance Resistance.FiniteNetwork
open scoped BigOperators _root_.Topology

theorem finiteSourceEnergy_tendsto_completion20261011
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge)
    (resistances : ℕ → Edge → ℝ) (limitResistance : Edge → ℝ)
    (resistanceLimit : ∀ edge, Tendsto (fun index => resistances index edge) atTop (𝓝 (limitResistance edge)))
    (limitNonzero : ∀ edge, limitResistance edge ≠ 0)
    (potentials : ℕ → Vertex → ℝ) (limitPotential : Vertex → ℝ)
    (potentialLimit : ∀ vertex, Tendsto (fun index => potentials index vertex) atTop (𝓝 (limitPotential vertex))) :
    Tendsto (fun index => sourceComponentEnergy network (resistances index) (potentials index)) atTop
      (𝓝 (sourceComponentEnergy network limitResistance limitPotential)) := by
  unfold sourceComponentEnergy finiteEnergy
  apply tendsto_finset_sum
  intro edge _
  have inverseLimit := (resistanceLimit edge).inv₀ (limitNonzero edge)
  have differenceLimit := ((potentialLimit (network.endpoint edge).1).sub
    (potentialLimit (network.endpoint edge).2)).pow 2
  by_cases reachable : network.graph.Reachable network.source (network.endpoint edge).1
  · simp only [if_pos reachable]
    exact inverseLimit.mul differenceLimit
  · simp only [if_neg reachable, zero_mul]
    exact tendsto_const_nhds

/-- The original unit-edge block responses determine the actual finite
trace quadratic form. Its coefficients converge to stationary electrical
conductances on every fixed coarse source component, including branches. -/
theorem actual_fixed_coarse_trace_energy_tendsto_completion20261011
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldPositive : ∀ address, 0 < field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) (potential : Fin (rule.generation coarse).vertices → ℝ) :
    Tendsto (fun fine => sourceComponentEnergy
      (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
      (fun edge => (growth ^ (coarse + fine + 2))⁻¹ *
        unitConfigurationResistance (rule.generation fine).network
          (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val)) potential)
      atTop (𝓝 (sourceComponentEnergy
        (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
        (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) potential)) := by
  apply finiteSourceEnergy_tendsto_completion20261011
  · intro edge
    exact actual_marked_block_resistance_limit rule marks crossing growth field fieldLimit coarse edge
  · intro edge
    apply ne_of_gt
    exact mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)
  · intro vertex
    exact tendsto_const_nhds

end
end IGSIII34.Diffusion
