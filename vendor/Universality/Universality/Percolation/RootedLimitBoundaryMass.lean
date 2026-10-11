import Universality.Percolation.RootedLimitSizeLaw

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem clusterSizeBirthSeries_mass_summable (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Summable (fun size : ℕ => (size : ℝ) * rule.clusterSizeBirthSeries p size) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hscale : ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) ≠ 0 :=
    (div_pos (sub_pos.mpr hm) (sub_pos.mpr hv)).ne'
  have hs := (rule.limitingRootSizeProbability_summable hedges hvertices hp hp').div_const
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2))
  exact hs.congr (fun size => by
    unfold limitingRootSizeProbability
    field_simp [(sub_pos.mpr hm).ne', (sub_pos.mpr hv).ne'])

theorem birth_mass_hasSum (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    HasSum (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) *
      ∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n)
      (∑' size : ℕ, (size : ℝ) * rule.clusterSizeBirthSeries p size) := by
  have hnonneg (pair : ℕ × ℕ) : 0 ≤
      (pair.1 : ℝ) * ((1 / (rule.edges : ℝ)) ^ (pair.2 + 1) *
        rule.expectedClusterBirth p pair.1 pair.2) := by
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
      (rule.expectedClusterBirth_bounds hp hp' _ _).1)
  have hdouble : Summable (fun pair : ℕ × ℕ =>
      (pair.1 : ℝ) * ((1 / (rule.edges : ℝ)) ^ (pair.2 + 1) *
        rule.expectedClusterBirth p pair.1 pair.2)) := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    constructor
    · intro size
      exact (rule.clusterSizeBirthSeries_summable hedges hp hp' size).mul_left (size : ℝ)
    · simpa only [tsum_mul_left, clusterSizeBirthSeries] using
        rule.clusterSizeBirthSeries_mass_summable hedges hvertices hp hp'
  have hswap := Summable.tsum_comm (f := fun size n : ℕ =>
    (size : ℝ) * ((1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirth p size n)) hdouble
  have hrew (n : ℕ) : (∑' size : ℕ,
      (size : ℝ) * ((1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirth p size n)) =
      (1 / (rule.edges : ℝ)) ^ (n + 1) *
        ∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro size
    ring
  have hs := hdouble.prod_symm.prod.hasSum
  simp only [Prod.swap_prod_mk, hrew] at hs
  simp only [tsum_mul_left, hrew] at hswap
  rw [hswap] at hs
  exact hs

theorem generation_internal_mass_density_limit (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalClusterMass p /
      ((rule.generation n).vertices : ℝ)) atTop
      (𝓝 (∑' size : ℕ, rule.limitingRootSizeProbability p size)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hmass := (rule.birth_mass_hasSum hedges hvertices hp hp').tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, ← rule.generation_internal_mass_birth_sum (by omega) p] at hmass
  have hquotient := hmass.div (rule.generation_volume_ratio_tendsto hedges)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  have hquot (n : ℕ) :
      ((rule.generation n).network.expectedInternalClusterMass p / (rule.edges : ℝ) ^ (n + 1)) /
        (((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1)) =
      (rule.generation n).network.expectedInternalClusterMass p /
        ((rule.generation n).vertices : ℝ) := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ (lt_trans zero_lt_one hm).ne')]
  have hvalue : (∑' size : ℕ, (size : ℝ) * rule.clusterSizeBirthSeries p size) /
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) =
      ∑' size : ℕ, rule.limitingRootSizeProbability p size := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro size
    unfold limitingRootSizeProbability
    field_simp [(sub_pos.mpr hm).ne', (sub_pos.mpr hv).ne']
  rw [hvalue] at hquotient
  convert hquotient using 1
  ext n
  exact (hquot n).symm

/-- The escaping mass of the actual finite uniform-root laws equals the
thermodynamic limit of the mass attached to the two planting terminals.
No infinite rooted graph or interchange of volume and cutoff is assumed. -/
theorem generation_boundary_mass_density_limit (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalBoundaryMass p /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 (rule.escapingRootMass p)) := by
  have hmass := rule.generation_internal_mass_density_limit hedges hvertices hp hp'
  have hterminals := (rule.generation_inverse_volume_tendsto_zero hedges hvertices).const_mul 2
  have hlimit := ((tendsto_const_nhds (x := (1 : ℝ))).sub hmass).sub hterminals
  simp only [mul_zero, sub_zero] at hlimit
  change Tendsto _ atTop (𝓝 (1 - ∑' size, rule.limitingRootSizeProbability p size))
  convert hlimit using 1
  ext n
  have hpartition := (rule.generation n).network.expectedInternalClusterMass_partition p
  have hvolume : ((rule.generation n).vertices : ℝ) ≠ 0 := by
    have := (rule.generation n).network.two_le_vertices
    exact_mod_cast (by omega : (rule.generation n).vertices ≠ 0)
  field_simp [hvolume]
  linarith

end
end Universality.Rule
