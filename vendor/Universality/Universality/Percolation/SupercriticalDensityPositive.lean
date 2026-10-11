import Universality.Percolation.ConnectedMassIterationLower
import Universality.Analysis.PositiveProductRecursion
import Universality.Percolation.UniformGenerationVolume
import Universality.Percolation.RootedLimitBoundaryMass

namespace Universality.Rule
noncomputable section
open FiniteNetwork Filter
open scoped Topology
set_option maxHeartbeats 0

theorem Classical.supercritical_escaping_root_mass_pos {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hpc : critical < p) (hp' : p < 1) : 0 < rule.escapingRootMass p := by
  have hp : 0 < p := hc.trans hpc
  have hedges : 0 < (rule.edges : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  let crossing (n : ℕ) := (rule.generation n).network.reliability p
  let connectedDensity (n : ℕ) := crossing n *
    (rule.generation n).network.conditionalVertexMass p .connected / (rule.edges : ℝ) ^ n
  have hcrossing (n : ℕ) : 0 < crossing n :=
    ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr ((h.generation n).connected _)
  have hcrossingLess (n : ℕ) : crossing n < 1 := (rule.generation n).network.reliability_lt_one hp hp'
  have hsummable : Summable (fun n => 1 - crossing n) := by
    simpa only [one_pow, one_mul] using
      h.supercritical_generation_failure_weighted_summable critical p 1 hc hc' hfixed hpc hp'.le zero_lt_one
  have hstart : 0 < connectedDensity 0 := by
    dsimp [connectedDensity, crossing]
    rw [pow_zero, div_one]
    change 0 < rule.network.reliability p * rule.network.conditionalVertexMass p .connected
    exact mul_pos (hcrossing 0) (rule.network.conditionalVertexMass_pos hp hp' (h.connected _) h.scale .connected)
  have hstep (n : ℕ) : crossing n ^ (rule.edges - 1) * connectedDensity n ≤ connectedDensity (n + 1) := by
    have hrec := h.generation_connected_mass_allOpen_lower p hp hp' n
    have hpower : crossing n ^ rule.edges = crossing n ^ (rule.edges - 1) * crossing n := by
      rw [← pow_succ]
      congr 1
      have := h.edges_gt_one
      omega
    dsimp [connectedDensity]
    apply (le_div_iff₀ (pow_pos hedges (n + 1))).mpr
    calc
      _ = (rule.edges : ℝ) * crossing n ^ rule.edges *
          (rule.generation n).network.conditionalVertexMass p .connected := by
        rw [hpower, pow_succ]
        field_simp [hedges.ne']
        <;> ring
      _ ≤ _ := hrec
  obtain ⟨lower, hlower, hbound⟩ := positive_lower_of_multiplicative_recursion
    crossing connectedDensity (rule.edges - 1) hcrossing hsummable hstart hstep
  obtain ⟨upper, hupper, hvolume⟩ := h.generation_volume_uniform_bound
  have hpoint (n : ℕ) : lower / upper ≤
      (rule.generation n).network.expectedInternalBoundaryMass p / ((rule.generation n).vertices : ℝ) := by
    have hmass : lower * (rule.edges : ℝ) ^ n ≤
        crossing n * (rule.generation n).network.conditionalVertexMass p .connected :=
      (le_div_iff₀ (pow_pos hedges n)).mp (hbound n)
    have hboundary : crossing n * (rule.generation n).network.conditionalVertexMass p .connected ≤
        (rule.generation n).network.expectedInternalBoundaryMass p := by
      rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate p (hcrossing n) (hcrossingLess n)]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (hcrossingLess n).le)
        ((rule.generation n).network.conditionalInternalMean_nonneg p hp.le hp'.le _ _ _))
    have hvolumePositive : 0 < ((rule.generation n).vertices : ℝ) := by
      have hv := (rule.generation n).network.two_le_vertices
      exact_mod_cast (show 0 < (rule.generation n).vertices by omega)
    apply (div_le_div_iff₀ hupper hvolumePositive).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hvolume n) hlower.le,
      mul_le_mul_of_nonneg_right (hmass.trans hboundary) hupper.le]
  have hlimit := rule.generation_boundary_mass_density_limit h.edges_gt_one h.vertices_gt_two hp.le hp'.le
  exact (div_pos hlower hupper).trans_le (le_of_tendsto_of_tendsto tendsto_const_nhds hlimit (Eventually.of_forall hpoint))

end
end Universality.Rule
