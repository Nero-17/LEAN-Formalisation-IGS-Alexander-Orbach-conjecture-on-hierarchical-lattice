import Universality.Percolation.RadiusSupport
import Universality.Percolation.AnnealedCriticalMomentFinite

namespace Universality
noncomputable section
set_option maxHeartbeats 800000

theorem summable_geometric_tail_bound (sequence : ℕ → ℝ) (ratio constant : ℝ)
    (hratio : 0 ≤ ratio) (hratio' : ratio < 1) (hconstant : 0 ≤ constant)
    (hsum : Summable sequence) (cutoff : ℕ)
    (hzero : ∀ n, n < cutoff → sequence n = 0)
    (hbound : ∀ n, sequence (n + cutoff) ≤ constant * ratio ^ n) :
    (∑' n, sequence n) ≤ constant / (1 - ratio) := by
  rw [← hsum.sum_add_tsum_nat_add cutoff]
  have hprefix : (∑ n ∈ Finset.range cutoff, sequence n) = 0 :=
    Finset.sum_eq_zero (fun n hn => hzero n (Finset.mem_range.mp hn))
  rw [hprefix, zero_add]
  have ht := ((summable_nat_add_iff cutoff).mpr hsum).tsum_le_tsum hbound
    ((summable_geometric_of_lt_one hratio hratio').mul_left constant)
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one hratio hratio', div_eq_mul_inv] using ht

end
end Universality

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem Classical.radius_tail_geometric_upper {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ bound : ℕ, 0 < bound ∧ ∃ upper : ℝ, 0 < upper ∧ ∀ n,
      rule.limitingRootRadiusTailProbability p
        (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n + 1) ≤
      upper * (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        (rule.edges : ℝ)) ^ n := by
  obtain ⟨bound, hbound, hsupport⟩ := h.radius_birth_support
  obtain ⟨constant, hconstant, hmass⟩ := h.birth_moment_upper_bound p hp hp' hfixed 1 (by omega)
  let growth := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let ratio := growth / (rule.edges : ℝ)
  have hgrowth : 0 ≤ growth := ENNReal.toReal_nonneg
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (by have := h.edges_gt_one; omega : 0 < rule.edges)
  have hratio : 0 ≤ ratio := div_nonneg hgrowth hm.le
  have hratio' : ratio < 1 := (div_lt_one hm).mpr (h.mass_spectralRadius_lt_edges p hp hp')
  have hscale : 0 < ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) := by
    apply div_pos
    · exact sub_pos.mpr (by exact_mod_cast h.edges_gt_one)
    · exact sub_pos.mpr (by exact_mod_cast h.vertices_gt_two)
  refine ⟨bound, hbound, ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
    (constant / (rule.edges : ℝ) ^ 2 / (1 - ratio)), mul_pos hscale (by positivity), ?_⟩
  intro n
  have htail := summable_geometric_tail_bound
    (fun k : ℕ => (1 / (rule.edges : ℝ)) ^ (k + 1) * rule.expectedRadiusBirth p
      (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n + 1) k)
    ratio (constant / (rule.edges : ℝ) ^ 2 * ratio ^ n) hratio hratio' (by positivity)
    (rule.radius_birth_series_summable h.edges_gt_one h.vertices_gt_two hp.le hp'.le _) (n + 1)
  have hzero : ∀ k, k < n + 1 →
      (1 / (rule.edges : ℝ)) ^ (k + 1) * rule.expectedRadiusBirth p
        (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n + 1) k = 0 := by
    intro k hk
    rw [hsupport k p _ (by
      have hpower := Nat.pow_le_pow_right (by have := h.scale; omega : 0 < rule.network.fullGraph.dist rule.network.source rule.network.target)
        (show k ≤ n by omega)
      have hmul := Nat.mul_le_mul_left bound hpower
      omega), mul_zero]
  have hterm (k : ℕ) :
      (1 / (rule.edges : ℝ)) ^ ((k + (n + 1)) + 1) * rule.expectedRadiusBirth p
        (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n + 1) (k + (n + 1)) ≤
      (constant / (rule.edges : ℝ) ^ 2 * ratio ^ n) * ratio ^ k := by
    have hpoint := (rule.expectedRadiusBirth_bounds hp.le hp'.le
      (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n + 1) (k + (n + 1))).2
    have hupper : rule.expectedClusterBirthPower p 1 (k + (n + 1)) ≤ constant * growth ^ (k + n) := by
      simpa only [Nat.add_assoc, one_mul] using hmass (k + n)
    calc
      _ ≤ (1 / (rule.edges : ℝ)) ^ ((k + (n + 1)) + 1) * (constant * growth ^ (k + n)) :=
        mul_le_mul_of_nonneg_left (hpoint.trans hupper) (by positivity)
      _ = _ := by
        simp only [ratio, div_pow, one_div_pow, pow_add, pow_succ]
        field_simp
        <;> ring
  have hfinal := mul_le_mul_of_nonneg_left (htail hzero hterm) hscale.le
  calc
    _ ≤ (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ((constant / (rule.edges : ℝ) ^ 2 * ratio ^ n) / (1 - ratio)) := hfinal
    _ = _ := by dsimp only [ratio, growth]; ring

end
end Universality.Rule
