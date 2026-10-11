import IGSIII34.Diffusion.ActualEnergyLiminfCompletion20261011
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

/-- Bounded real functions on a countable set admit one strictly selected
subsequence converging at every point simultaneously. -/
theorem bounded_countable_potentials_subsequence_completion20261011
    {Point : Type*} [Countable Point] (potentials : ℕ → Point → ℝ) (bound : ℝ)
    (bounded : ∀ index point, |potentials index point| ≤ bound) :
    ∃ limitPotential : Point → ℝ, ∃ selected : ℕ → ℕ,
      StrictMono selected ∧ (∀ point, |limitPotential point| ≤ bound) ∧
      ∀ point, Tendsto (fun index => potentials (selected index) point) atTop (𝓝 (limitPotential point)) := by
  let values : ℕ → Point → Set.Icc (-bound) bound := fun index point =>
    ⟨potentials index point, abs_le.mp (bounded index point)⟩
  obtain ⟨limit, _, selected, strict, convergence⟩ :=
    (isCompact_univ (X := Point → Set.Icc (-bound) bound)).tendsto_subseq
      (x := values) (fun _ => Set.mem_univ _)
  refine ⟨fun point => (limit point).val, selected, strict,
    (fun point => abs_le.mpr (limit point).property), fun point => ?_⟩
  have coordinate := (continuous_apply point).tendsto limit |>.comp convergence
  exact continuous_subtype_val.continuousAt.tendsto.comp coordinate

theorem countable_actualEnergySkeleton_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks}) :
    Countable (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryEnergySkeleton ElectricalSkeleton
  infer_instance

end
end IGSIII34.Diffusion
