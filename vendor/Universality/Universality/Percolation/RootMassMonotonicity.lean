import Universality.Percolation.SupercriticalDensityPositive
import Universality.Percolation.BernoulliMonotonicity
import Universality.Percolation.SubcriticalRootMass

namespace Universality.Rule
noncomputable section
open FiniteNetwork Filter
open scoped Topology

theorem escapingRootMass_monotoneOn (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) :
    MonotoneOn rule.escapingRootMass (Set.Icc 0 1) := by
  intro p hp q hq hpq
  apply le_of_tendsto_of_tendsto
    (rule.generation_boundary_mass_density_limit hedges hvertices hp.1 hp.2)
    (rule.generation_boundary_mass_density_limit hedges hvertices hq.1 hq.2)
  apply Eventually.of_forall
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hm := (rule.generation n).network.expectedInternalBoundaryMoment_monotoneOn 1 hp hq hpq
  simpa only [expectedInternalBoundaryMoment, expectedInternalBoundaryMass, pow_one] using hm

theorem Classical.escapingRootMass_pos_iff {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 < rule.escapingRootMass p ↔ critical < p := by
  constructor
  · intro hpositive
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hmono := rule.escapingRootMass_monotoneOn h.edges_gt_one h.vertices_gt_two
      ⟨hp, hp'⟩ ⟨hc.le, hc'.le⟩ hle
    rw [h.critical_escapingRootMass_zero critical hc hc' hfixed] at hmono
    exact (not_lt_of_ge hmono) hpositive
  · intro hpc
    let middle := (critical + p) / 2
    have hmiddle : critical < middle := by dsimp [middle]; linarith
    have hmiddle' : middle < 1 := by dsimp [middle]; linarith
    have hmiddlep : middle ≤ p := by dsimp [middle]; linarith
    exact (h.supercritical_escaping_root_mass_pos critical middle hc hc' hfixed hmiddle hmiddle').trans_le
      (rule.escapingRootMass_monotoneOn h.edges_gt_one h.vertices_gt_two
        ⟨(hc.trans hmiddle).le, hmiddle'.le⟩ ⟨hp, hp'⟩ hmiddlep)

end
end Universality.Rule
