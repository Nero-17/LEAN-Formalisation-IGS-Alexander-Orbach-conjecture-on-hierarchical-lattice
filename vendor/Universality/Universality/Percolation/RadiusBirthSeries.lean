import Universality.Percolation.RadiusEquivalence
import Universality.Percolation.RadiusBoundaryBounds
import Universality.Percolation.RootedLimitBoundaryMass

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter FiniteNetwork
open scoped Topology

def expectedRadiusBirth (rule : Rule) (p : ℝ) (radius : ℕ) : ℕ → ℝ
  | 0 => rule.network.expectedInternalRadiusRootCount p radius
  | n + 1 => rule.network.expectedBirthRadiusRootCount (rule.generation n).network p radius

def limitingRootRadiusTailProbability (rule : Rule) (p : ℝ) (radius : ℕ) : ℝ :=
  ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
    ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedRadiusBirth p radius n

theorem expectedRadiusBirth_bounds (rule : Rule) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (radius n : ℕ) :
    0 ≤ rule.expectedRadiusBirth p radius n ∧
      rule.expectedRadiusBirth p radius n ≤ rule.expectedClusterBirthPower p 1 n := by
  cases n with
  | zero =>
    constructor
    · exact Finset.sum_nonneg (fun configuration _ => mul_nonneg
        (bernoulliWeight_nonneg hp hp' configuration) (Nat.cast_nonneg _))
    · unfold expectedRadiusBirth expectedInternalRadiusRootCount expectedClusterBirthPower
        expectedInternalClusterPower
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' configuration)
      simp only [internalRadiusRootCount, Nat.cast_sum, pow_one]
      exact Finset.sum_le_sum (fun cluster _ => by
        exact_mod_cast rule.network.clusterRadiusRootCount_le_card cluster radius)
  | succ n =>
    constructor
    · exact Finset.sum_nonneg (fun configuration _ => mul_nonneg
        (bernoulliWeight_nonneg hp hp' configuration) (Nat.cast_nonneg _))
    · exact rule.network.expectedBirthRadiusRootCount_le_mass _ hp hp' radius

theorem radius_birth_series_summable (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedRadiusBirth p radius n) := by
  have hmass := (rule.birth_mass_hasSum hedges hvertices hp hp').summable
  have hidentity (n : ℕ) : (∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n) =
      rule.expectedClusterBirthPower p 1 n := by
    simpa only [pow_one] using (rule.expectedClusterBirthPower_hasSum p 1 n).tsum_eq
  simp_rw [hidentity] at hmass
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity)
    (rule.expectedRadiusBirth_bounds hp hp' radius n).1) _ hmass
  intro n
  exact mul_le_mul_of_nonneg_left (rule.expectedRadiusBirth_bounds hp hp' radius n).2 (by positivity)

theorem Classical.generation_radius_normalized {rule : Rule} (h : rule.Classical)
    (p : ℝ) (radius n : ℕ) :
    (rule.generation n).network.expectedInternalRadiusRootCount p radius / (rule.edges : ℝ) ^ (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (1 / (rule.edges : ℝ)) ^ (k + 1) * rule.expectedRadiusBirth p radius k := by
  have hm : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast (by have := h.edges_gt_one; omega : rule.edges ≠ 0)
  induction n with
  | zero =>
    change rule.network.expectedInternalRadiusRootCount p radius / (rule.edges : ℝ) ^ (0 + 1) = _
    simp [expectedRadiusBirth, div_eq_mul_inv, mul_comm]
  | succ n ih =>
    rw [h.generation_expectedInternalRadiusRootCount, Finset.sum_range_succ, ← ih]
    simp only [expectedRadiusBirth, pow_succ, one_div_pow]
    field_simp
    <;> ring

theorem Classical.generation_internal_radius_density_tendsto {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalRadiusRootCount p radius /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 (rule.limitingRootRadiusTailProbability p radius)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hs := (rule.radius_birth_series_summable h.edges_gt_one h.vertices_gt_two hp hp' radius).hasSum.tendsto_sum_nat
  have hshift := hs.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, ← h.generation_radius_normalized p radius] at hshift
  have hquotient := hshift.div (rule.generation_volume_ratio_tendsto h.edges_gt_one)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  convert hquotient using 1
  · ext n
    exact (div_div_div_cancel_right₀ (pow_ne_zero (n + 1) (lt_trans zero_lt_one hm).ne') _ _).symm
  · congr 1
    unfold limitingRootRadiusTailProbability
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

theorem Classical.uniformVertexRadiusTailProbability_tendsto {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) (radius : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.uniformVertexRadiusTailProbability p radius)
      atTop (𝓝 (rule.limitingRootRadiusTailProbability p radius)) := by
  have hboundary := h.expected_boundary_mass_density_tendsto_zero p hp hp' hfixed
  have hterminals := (rule.generation_inverse_volume_tendsto_zero h.edges_gt_one h.vertices_gt_two).const_mul 2
  have hupper := hboundary.add hterminals
  simp only [mul_zero, add_zero] at hupper
  have herror : Tendsto (fun n : ℕ => (rule.generation n).network.uniformVertexRadiusTailProbability p radius -
      (rule.generation n).network.expectedInternalRadiusRootCount p radius / (rule.generation n).vertices)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ((rule.generation n).network.uniformVertexRadiusTailProbability_boundary_bounds hp.le hp'.le radius).1)
      (fun n => ((rule.generation n).network.uniformVertexRadiusTailProbability_boundary_bounds hp.le hp'.le radius).2)
    simpa only [add_div, mul_one_div] using hupper
  have hsum := (h.generation_internal_radius_density_tendsto hp.le hp'.le radius).add herror
  convert hsum using 1
  · ext n; ring
  · simp only [add_zero]

end
end Universality.Rule
