import Universality.Analysis.SmoothRenormalization
import Universality.Percolation.ClusterNumberSecondDerivativeEquation
import Universality.Percolation.ClusterNumberAlphaCriterion
import Mathlib.Analysis.Analytic.Polynomial

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology ContDiff

/-- The actual cluster density is C^j at criticality whenever its thermal
multiplier to order j is strictly below the volume multiplier. -/
theorem Classical.cluster_number_contDiffAt {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ)) :
    ContDiffAt ℝ order rule.network.clusterNumberAnalyticExtension critical := by
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing : Polynomial ℝ := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  let normalization : ℝ := ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)
  have hmass : (0 : ℝ) < rule.edges := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  have hcrossing : crossing.eval = rule.network.reliability := by
    funext p
    simp only [crossing, Polynomial.eval_map, reliabilityPolynomial_eval]
  have hforcing (p : ℝ) : forcing.eval p = rule.network.expectedInternalClusterNumber p := by
    simp only [forcing, Polynomial.eval_map, internalClusterPolynomial_eval]
  have hiteration : AnalyticAt ℝ rule.network.reliability critical := by
    rw [← hcrossing]
    exact (AnalyticOnNhd.eval_polynomial crossing) critical (mem_univ _)
  have hmaps : MapsTo rule.network.reliability (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro p hp
    exact (rule.network.unitReliability ⟨p, hp⟩).property
  have hescape : ∃ radius : ℝ, 0 < radius ∧ ∀ p ∈ Icc (0 : ℝ) 1,
      p ≠ critical → ∃ depth : ℕ, radius ≤ |rule.network.reliability^[depth] p - critical| := by
    obtain ⟨radius, hradius, hexit⟩ := h.unitReliability_escape critical hc hc' hfixed
    refine ⟨radius, hradius, ?_⟩
    intro p hp hne
    obtain ⟨depth, hdepth⟩ := hexit ⟨p, hp⟩ (fun heq => hne (congrArg Subtype.val heq))
    exact ⟨depth, by simpa only [Subtype.dist_eq, Real.dist_eq,
      rule.network.unitReliability_iterate_val] using hdepth⟩
  apply contDiffAt_of_repelling_renormalization order rule.network.reliability 0 1 critical hc hc'
    hmaps hiteration hfixed
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale)
    (fun p hp hne => h.reliability_ne_critical critical p hc hc' hfixed hp.1 hp.2 hne) hescape
    rule.network.clusterNumberAnalyticExtension (fun _ => 1 / (rule.edges : ℝ))
    (fun p => normalization * forcing.eval p / (rule.edges : ℝ))
    (h.cluster_number_analyticExtension_hasDerivAt_critical critical hc hc' hfixed).continuousAt
    (fun p hp hne => h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1 hp.2 hne)
    analyticAt_const
  · exact ((analyticAt_const.mul ((AnalyticOnNhd.eval_polynomial forcing) critical (mem_univ _))).div_const
      (c := (rule.edges : ℝ))).contDiffAt
  · filter_upwards [Ioo_mem_nhds hc hc'] with p hp
    have hnext := rule.network.clusterNumberAnalyticExtension_eq
      (rule.network.unitReliability ⟨p, hp.1.le, hp.2.le⟩)
    change rule.network.clusterNumberAnalyticExtension (rule.network.reliability p) = _ at hnext
    rw [rule.network.clusterNumberAnalyticExtension_eq ⟨p, hp.1.le, hp.2.le⟩, hnext]
    have heq := rule.network.clusterNumberSeries_equation h.edges_gt_one ⟨p, hp.1.le, hp.2.le⟩
    rw [hforcing]
    rw [one_div_mul_eq_div, ← add_div]
    apply (eq_div_iff hmass.ne').mpr
    dsimp [normalization]
    nlinarith
  · rw [abs_of_pos (one_div_pos.mpr hmass), one_div_mul_eq_div]
    exact (div_lt_one hmass).mpr hthreshold

/-- The raw-alpha clause for the actual density. Local regularity is proved
from the thermal/volume threshold, rather than assumed. -/
theorem Classical.cluster_number_raw_alpha_criterion {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 3 ≤ order)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ))
    (hvanish : ∀ i, 3 ≤ i → i < order →
      iteratedDeriv i rule.network.clusterNumberAnalyticExtension critical = 0)
    (hleading : iteratedDeriv order rule.network.clusterNumberAnalyticExtension critical ≠ 0) :
    ((∀ᶠ p in 𝓝[<] critical, iteratedDeriv 3 rule.network.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 rule.network.clusterNumberAnalyticExtension p| /
        Real.log |p - critical|) (𝓝[<] critical) (𝓝 (2 - (order : ℝ)))) ∧
    ((∀ᶠ p in 𝓝[>] critical, iteratedDeriv 3 rule.network.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 rule.network.clusterNumberAnalyticExtension p| /
        Real.log |p - critical|) (𝓝[>] critical) (𝓝 (2 - (order : ℝ)))) :=
  raw_cluster_number_alpha_criterion rule.network.clusterNumberAnalyticExtension critical order horder
    (h.cluster_number_contDiffAt critical hc hc' hfixed order hthreshold) hvanish hleading

end
end Universality.Rule

