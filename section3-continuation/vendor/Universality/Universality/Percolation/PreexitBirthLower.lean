import Universality.Percolation.PreexitBoundaryComparison
import Universality.Percolation.AnnealedBirthMomentLower

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- A uniform positive first-birth-mass lower bound after finitely many
initial levels. Two further orbit indices are retained explicitly. -/
theorem Classical.preexit_birth_first_moment_eventual_lower {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius lower : ℝ, 0 < radius ∧ 0 < lower ∧ ∃ start : ℕ,
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ, start ≤ n →
        (∀ j ≤ n + 2, |rule.network.reliability^[j] p - critical| < radius) →
          lower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ n ≤
            rule.expectedClusterBirthPower p 1 (n + 1) := by
  let growth := (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal
  have hgrowth : 1 < growth :=
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hgap : growth < (rule.edges : ℝ) := h.mass_spectralRadius_lt_edges critical hc hc'
  have hgapNear : ∀ᶠ distortion : ℝ in 𝓝 1,
      0 < (rule.edges : ℝ) - distortion ^ 4 * growth :=
    (show ContinuousAt (fun distortion : ℝ => (rule.edges : ℝ) - distortion ^ 4 * growth) 1 by fun_prop).eventually
      (lt_mem_nhds (by simpa using sub_pos.mpr hgap))
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.eventually_nhds_iff.mp hgapNear
  let distortion : ℝ := 1 + epsilon / 2
  have hd : 1 < distortion := by dsimp [distortion]; linarith
  have hdpos : 0 < distortion := zero_lt_one.trans hd
  have hdistortion : 0 < (rule.edges : ℝ) - distortion ^ 4 * growth := by
    apply hball (y := distortion)
    simp only [Real.dist_eq]
    dsimp [distortion]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hepsilon)]
    linarith
  have hcoefficient : 0 < (rule.edges : ℝ) / distortion ^ 2 - distortion ^ 2 * growth := by
    have heq : (rule.edges : ℝ) / distortion ^ 2 - distortion ^ 2 * growth =
        ((rule.edges : ℝ) - distortion ^ 4 * growth) / distortion ^ 2 := by
      field_simp [hdpos.ne']
      <;> ring
    rw [heq]
    exact div_pos hdistortion (sq_pos_of_pos hdpos)
  obtain ⟨limit, hlimitPositive, hlimit⟩ := h.boundary_mass_normalized_mean_limit critical hc hc' hfixed
  change Tendsto (fun n => (rule.generation n).network.expectedInternalBoundaryMass critical / growth ^ n) atTop (𝓝 limit) at hlimit
  have hsequence := (hlimit.const_mul ((rule.edges : ℝ) / distortion ^ 2)).sub
    ((hlimit.comp (tendsto_add_atTop_nat 1)).const_mul (distortion ^ 2 * growth))
  have hpositive : 0 < (rule.edges : ℝ) / distortion ^ 2 * limit - distortion ^ 2 * growth * limit := by
    nlinarith [mul_pos hcoefficient hlimitPositive]
  obtain ⟨start, hstart⟩ := eventually_atTop.mp
    (hsequence.eventually (Ioi_mem_nhds (half_lt_self hpositive)))
  obtain ⟨radius, hradius, hcomparison⟩ := h.preexit_boundary_mean_comparison critical hc hc' hfixed distortion hd
  refine ⟨radius, ((rule.edges : ℝ) / distortion ^ 2 * limit - distortion ^ 2 * growth * limit) / 2,
    hradius, half_pos hpositive, start, ?_⟩
  intro p hp hp' n hn horbit
  have hbefore := (hcomparison p hp hp' n (fun j hj => horbit j (by omega))).2
  have hafter := (hcomparison p hp hp' (n + 1) (fun j hj => horbit j (by omega))).1
  have hcurrent : (rule.generation n).network.expectedInternalBoundaryMass critical / distortion ^ 2 ≤
      (rule.generation n).network.expectedInternalBoundaryMass p :=
    (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr (by simpa only [mul_comm] using hbefore)
  have hcurrentWeighted := mul_le_mul_of_nonneg_left hcurrent (Nat.cast_nonneg rule.edges)
  have hsequenceBound := (hstart n hn).le
  change _ ≤ (rule.edges : ℝ) / distortion ^ 2 *
      ((rule.generation n).network.expectedInternalBoundaryMass critical / growth ^ n) -
        (distortion ^ 2 * growth) *
          ((rule.generation (n + 1)).network.expectedInternalBoundaryMass critical / growth ^ (n + 1)) at hsequenceBound
  have hidentity : (rule.edges : ℝ) / distortion ^ 2 *
      ((rule.generation n).network.expectedInternalBoundaryMass critical / growth ^ n) -
        (distortion ^ 2 * growth) *
          ((rule.generation (n + 1)).network.expectedInternalBoundaryMass critical / growth ^ (n + 1)) =
      ((rule.edges : ℝ) * ((rule.generation n).network.expectedInternalBoundaryMass critical / distortion ^ 2) -
        distortion ^ 2 * (rule.generation (n + 1)).network.expectedInternalBoundaryMass critical) / growth ^ n := by
    rw [pow_succ]
    field_simp [(zero_lt_one.trans hgrowth).ne', hdpos.ne']
    <;> ring
  rw [hidentity] at hsequenceBound
  have hmassLower := (le_div_iff₀ (pow_pos (zero_lt_one.trans hgrowth) n)).mp hsequenceBound
  rw [rule.expectedClusterBirthPower_one_boundary_difference]
  have hvertices : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  change _ ≤ (rule.vertices : ℝ) - 2 + (rule.edges : ℝ) *
    (rule.generation n).network.expectedInternalBoundaryMass p -
      (rule.generation (n + 1)).network.expectedInternalBoundaryMass p
  linarith


theorem Classical.preexit_birth_moment_eventual_lower {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ start : ℕ, ∀ order : ℕ, 1 ≤ order → ∃ lower : ℝ, 0 < lower ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ, start ≤ n →
        (∀ j ≤ n + 2, |rule.network.reliability^[j] p - critical| < radius) →
          lower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) ≤
            rule.expectedClusterBirthPower p order (n + 1) := by
  obtain ⟨radius, firstLower, hradius, hfirstLower, start, hb⟩ :=
    h.preexit_birth_first_moment_eventual_lower critical hc hc' hfixed
  refine ⟨radius, hradius, start, ?_⟩
  intro order horder
  have hvertices : (0 : ℝ) < rule.vertices := by
    have := h.vertices_gt_two
    exact_mod_cast (by omega : 0 < rule.vertices)
  refine ⟨firstLower ^ order / (rule.vertices : ℝ) ^ (order - 1),
    div_pos (pow_pos hfirstLower _) (pow_pos hvertices _), ?_⟩
  intro p hp hp' n hn horbit
  have hmean := hb p hp hp' n hn horbit
  have hpower := pow_le_pow_left₀ (mul_nonneg hfirstLower.le (by positivity)) hmean order
  have hjensen := rule.network.expectedBirthClusterPower_mean_pow_le
    (rule.generation n).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p 1 (n + 1) ^ order ≤
    (rule.vertices : ℝ) ^ (order - 1) * rule.expectedClusterBirthPower p order (n + 1) at hjensen
  calc
    _ = (firstLower *
        ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ n) ^ order /
          (rule.vertices : ℝ) ^ (order - 1) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n order]
      ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hvertices (order - 1))).mpr
      (by simpa only [mul_comm (rule.expectedClusterBirthPower p order (n + 1))] using hpower.trans hjensen)

end
end Universality.Rule
