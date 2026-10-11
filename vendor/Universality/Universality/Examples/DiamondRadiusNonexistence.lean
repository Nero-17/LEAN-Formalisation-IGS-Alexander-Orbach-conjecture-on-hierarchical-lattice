import Universality.Examples.DiamondActualSpikes
import Universality.Analysis.RadiusPointNonexistence
import Universality.Percolation.CriticalRadiusPowerBounds

namespace Universality
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

theorem dyadic_radius_tail_power (growth : ℝ) (hpositive : 0 < growth) (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) ^ (-(Real.log 4 - Real.log growth) / Real.log 2) = (growth / 4) ^ n := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_def_of_pos (pow_pos (by norm_num) n), Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have heq : (n : ℝ) * Real.log 2 * (-(Real.log 4 - Real.log growth) / Real.log 2) =
      Real.log (growth / 4) * n := by
    rw [Real.log_div hpositive.ne' (by norm_num)]
    field_simp [hlog]
    <;> ring
  rw [heq, Real.exp_mul, Real.exp_log (div_pos hpositive (by norm_num)), Real.rpow_natCast]

theorem diamond_radius_point_log_limit_nonexistent
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : diamondNetwork.reliability p = p) :
    ¬ ∃ exponent : ℝ,
      (∀ᶠ radius : ℕ in atTop, 0 < diamondRule.limitingRootRadiusProbability p radius) ∧
      Tendsto (fun radius : ℕ => Real.log (diamondRule.limitingRootRadiusProbability p radius) /
        Real.log (radius : ℝ)) atTop (𝓝 exponent) := by
  let growth := (spectralRadius ℂ ((diamondNetwork.massMatrix p).map Complex.ofReal)).toReal
  let ratio := growth / 4
  have hgrowth : 0 < growth :=
    lt_of_le_of_lt (Nat.cast_nonneg _) (diamondRule_classical.terminal_degree_spectral_bounds p hp hp').2.1
  have hratio : 0 < ratio := div_pos hgrowth (by norm_num)
  obtain ⟨constant, hconstant, hspikes⟩ := diamond_actual_radius_spikes p hp hp' hfixed
  obtain ⟨lower, upper, hlower, hupper, htail⟩ := diamondRule_classical.critical_radius_power_bounds p hp hp' hfixed
  have hdyadic := tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
  apply no_point_log_limit_of_dyadic_spikes (diamondRule.limitingRootRadiusProbability p)
    (diamondRule.limitingRootRadiusProbability_nonneg diamondRule_classical.edges_gt_one
      diamondRule_classical.vertices_gt_two hp.le hp'.le)
    ratio (constant / ratio ^ 3) upper hratio (div_pos hconstant (pow_pos hratio _)) hupper
  filter_upwards [eventually_ge_atTop 3, hdyadic.eventually htail] with n hn htailn
  constructor
  · have hs := hspikes (n - 3)
    rw [Nat.sub_add_cancel hn] at hs
    have hpow : ratio ^ n = ratio ^ (n - 3) * ratio ^ 3 := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    have heq : constant / ratio ^ 3 * ratio ^ n = constant * ratio ^ (n - 3) := by
      rw [hpow]
      field_simp [hratio.ne']
      <;> ring
    rw [heq]
    exact hs
  · have hu := htailn.2
    change diamondRule.limitingRootRadiusTailProbability p (2 ^ n) ≤ upper *
      ((2 ^ n : ℕ) : ℝ) ^ (-(Real.log 4 - Real.log growth) /
        Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target : ℝ)) at hu
    rw [diamond_terminal_distance, Nat.cast_ofNat, dyadic_radius_tail_power growth hgrowth n] at hu
    rw [diamondRule.limitingRootRadiusProbability_partial_sum]
    exact (sub_le_self _ (diamondRule.limitingRootRadiusTailProbability_nonneg
      diamondRule_classical.edges_gt_one diamondRule_classical.vertices_gt_two hp.le hp'.le _)).trans hu

end
end Universality


