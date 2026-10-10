import Universality.Percolation.InternalClusterMass

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def expectedInternalClusterMass (p : ℝ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalClusterMass configuration

def expectedInternalBoundaryMass (p : ℝ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalSelectedMass true true configuration

theorem expectedInternalClusterMass_partition (p : ℝ) :
    R.expectedInternalClusterMass p + R.expectedInternalBoundaryMass p + 2 = vertices := by
  have h := congrArg (fun values : Configuration edges → ℝ =>
      ∑ configuration, bernoulliWeight p configuration * values configuration)
    (funext (R.internalClusterMass_partition))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight, one_mul] at h
  exact h

theorem expectedInternalBoundaryMass_disintegrate (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) :
    R.expectedInternalBoundaryMass p =
      R.reliability p * R.conditionalVertexMass p .connected +
        (1 - R.reliability p) * R.conditionalVertexMass p .both := by
  change _ = R.reliability p * R.conditionalInternalMean p true true false +
    (1 - R.reliability p) * R.conditionalInternalMean p false true true
  rw [← R.conditionalInternalMean_connected]
  unfold expectedInternalBoundaryMass conditionalInternalMean
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro configuration _
  unfold conditionalCellWeight
  cases hcross : R.crosses configuration <;>
    simp only [hcross, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;>
    field_simp [hpositive.ne', (sub_pos.mpr hless).ne']
  all_goals ring

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology

theorem generation_inverse_volume_tendsto_zero (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) :
    Tendsto (fun n : ℕ => 1 / ((rule.generation n).vertices : ℝ)) atTop (𝓝 0) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hpos : 0 < (rule.edges : ℝ) := lt_trans zero_lt_one hm
  have hpowers : Tendsto (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (one_div_nonneg.mpr hpos.le)
      ((div_lt_one hpos).mpr hm)).comp (tendsto_add_atTop_nat 1)
  have h := hpowers.div (rule.generation_volume_ratio_tendsto hedges)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  simp only [zero_div] at h
  convert h using 1
  ext n
  simp only [Pi.div_apply, one_div_pow, div_div_div_cancel_right₀ (pow_ne_zero _ hpos.ne')]

theorem Classical.expected_boundary_mass_density_tendsto_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalBoundaryMass p /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 0) := by
  have hfirst := (h.conditional_boundary_mass_density_tendsto_zero p hp hp' hfixed .connected).const_mul p
  have hsecond := (h.conditional_boundary_mass_density_tendsto_zero p hp hp' hfixed .both).const_mul (1 - p)
  have hsum := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hsum
  convert hsum using 1
  ext n
  rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate p
    (by rwa [rule.generation_fixed_point p hfixed]) (by rwa [rule.generation_fixed_point p hfixed]),
    rule.generation_fixed_point p hfixed, add_div, mul_div_assoc, mul_div_assoc]

theorem Classical.internal_cluster_mass_density_tendsto_one {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalClusterMass p /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 1) := by
  have hboundary := h.expected_boundary_mass_density_tendsto_zero p hp hp' hfixed
  have hterminals := (rule.generation_inverse_volume_tendsto_zero h.edges_gt_one h.vertices_gt_two).const_mul 2
  have hlimit := ((tendsto_const_nhds (x := (1 : ℝ))).sub hboundary).sub hterminals
  simp only [mul_zero, sub_zero] at hlimit
  convert hlimit using 1
  ext n
  have hpartition := (rule.generation n).network.expectedInternalClusterMass_partition p
  have hv : ((rule.generation n).vertices : ℝ) ≠ 0 := by
    have htwo := (rule.generation n).network.two_le_vertices
    exact_mod_cast (by omega : (rule.generation n).vertices ≠ 0)
  apply (div_eq_iff hv).mpr
  field_simp
  linarith

end
end Universality.Rule
