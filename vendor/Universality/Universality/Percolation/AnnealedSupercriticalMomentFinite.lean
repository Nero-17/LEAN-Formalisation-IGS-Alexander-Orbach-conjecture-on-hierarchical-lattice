import Universality.Percolation.SupercriticalBirthBound
import Universality.Percolation.SupercriticalFailureSummability

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

/-- Every finite-cluster moment of the actual limiting uniform-root size
law is finite at every supercritical parameter, including p = 1. -/
theorem Classical.supercritical_root_moment_ne_top {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hpc : critical < p) (hp' : p ≤ 1)
    (order : ℕ) : rule.limitingRootSizeMoment p order ≠ ⊤ := by
  have hp : 0 ≤ p := (hc.trans hpc).le
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := lt_trans zero_lt_one hm
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  let volumeBound : ℝ := ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) + 1
  have hvolumeBound : 0 < volumeBound := by
    exact add_pos (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)) zero_lt_one
  have hvolume : ∀ᶠ n : ℕ in atTop,
      ((rule.generation (n + 1)).vertices : ℝ) ≤ volumeBound * (rule.edges : ℝ) ^ ((n + 1) + 1) := by
    have hlimit := (rule.generation_volume_ratio_tendsto h.edges_gt_one).comp (tendsto_add_atTop_nat 1)
    filter_upwards [hlimit.eventually_le_const (lt_add_one
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)))] with n hn
    exact (div_le_iff₀ (pow_pos hmpos _)).mp hn
  apply (rule.limitingRootSizeMoment_finite_iff_birth_summable h.edges_gt_one h.vertices_gt_two hp hp' order).mpr
  apply (summable_nat_add_iff 1).mp
  have hfailure := h.supercritical_generation_failure_weighted_summable critical p
    ((rule.edges : ℝ) ^ (order + 1)) hc hc' hfixed hpc hp' (pow_pos hmpos _)
  have hmajor := hfailure.mul_left
    ((rule.vertices : ℝ) * volumeBound ^ (order + 1) * (rule.edges : ℝ) ^ (2 * (order + 1)) * rule.edges)
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [hvolume] with n hn
  have hnonneg := rule.expectedClusterBirthPower_nonneg hp hp' (order + 1) (n + 1)
  have hfailnonneg : 0 ≤ 1 - (rule.generation n).network.reliability p :=
    sub_nonneg.mpr ((rule.generation n).network.reliability_le_one hp hp')
  have hvertices : Fintype.card (rule.network.SubstitutionVertex (rule.generation n).network) =
      (rule.generation (n + 1)).vertices := by
    have hi := Fintype.card_congr (rule.generationTopDecomposition n).vertex
    simpa only [Fintype.card_fin] using hi.symm
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hnonneg)]
  calc
    _ ≤ rule.expectedClusterBirthPower p (order + 1) (n + 1) :=
      mul_le_of_le_one_left hnonneg (pow_le_one₀ (by positivity)
        ((div_le_one hmpos).mpr hm.le))
    _ ≤ (rule.vertices : ℝ) * ((rule.generation (n + 1)).vertices : ℝ) ^ (order + 1) *
        ((rule.edges : ℝ) * (1 - (rule.generation n).network.reliability p)) := by
      simpa only [expectedClusterBirthPower, hvertices] using
        rule.network.expectedBirthClusterPower_le_failure (rule.generation n).network h.connected hp hp' (order + 1)
    _ ≤ (rule.vertices : ℝ) * (volumeBound * (rule.edges : ℝ) ^ ((n + 1) + 1)) ^ (order + 1) *
        ((rule.edges : ℝ) * (1 - (rule.generation n).network.reliability p)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hmpos.le hfailnonneg)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn _
    _ = _ := by
      simp only [mul_pow, ← pow_mul]
      rw [show ((n + 1) + 1) * (order + 1) = 2 * (order + 1) + (order + 1) * n by ring,
        pow_add]
      ring

end
end Universality.Rule
