import Universality.Examples.WheatstoneRightExponent

namespace Universality
noncomputable section
open Set Filter
open scoped Topology

theorem wheatstone_cluster_number_third_derivative_reflection (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p +
      iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1 - p) = 0 := by
  have hlocal : (fun q => wheatstoneNetwork.clusterNumberAnalyticExtension q -
      wheatstoneNetwork.clusterNumberAnalyticExtension (1 - q)) =ᶠ[𝓝 p] (fun q => 1 - 2 * q) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    have hfirst := wheatstoneNetwork.clusterNumberAnalyticExtension_eq ⟨q, hq.1.le, hq.2.le⟩
    have hnext := wheatstoneNetwork.clusterNumberAnalyticExtension_eq
      (unitIntervalReflection ⟨q, hq.1.le, hq.2.le⟩)
    change wheatstoneNetwork.clusterNumberAnalyticExtension (1 - q) = _ at hnext
    rw [hfirst, hnext]
    exact wheatstone_clusterNumberSeries_reflection ⟨q, hq.1.le, hq.2.le⟩
  have hregular := wheatstone_cluster_number_contDiffAt_three p ⟨hp.1.le, hp.2.le⟩
  have hnext := wheatstone_cluster_number_contDiffAt_three (1 - p)
    (show 1 - p ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hp.2], by linarith [hp.1]⟩)
  have hnextRegular : ContDiffAt ℝ 3
      (fun q : ℝ => wheatstoneNetwork.clusterNumberAnalyticExtension (1 - q)) p := by
    simpa only [Function.comp_def] using hnext.comp p (contDiffAt_const.sub contDiffAt_id)
  have hjet := hlocal.iteratedDeriv_eq 3
  change iteratedDeriv 3 (wheatstoneNetwork.clusterNumberAnalyticExtension -
    (fun q => wheatstoneNetwork.clusterNumberAnalyticExtension (1 - q))) p = _ at hjet
  rw [iteratedDeriv_sub hregular hnextRegular,
    iteratedDeriv_comp_const_sub] at hjet
  have hlinear : iteratedDeriv 3 (fun q : ℝ => 1 - 2 * q) p = 0 := by
    have hpolynomial : ((1 - 2 * Polynomial.X : Polynomial ℝ).eval) = (fun q : ℝ => 1 - 2 * q) := by
      funext q
      simp
    rw [← hpolynomial, polynomial_iteratedDeriv_eval]
    norm_num [Function.iterate_succ_apply, Function.iterate_zero_apply,
      Polynomial.derivative_sub, Polynomial.derivative_mul]
  rw [hlinear] at hjet
  norm_num [smul_eq_mul] at hjet
  exact hjet

theorem wheatstone_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] (1 / 2 : ℝ), iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - 1 / 2|) (𝓝[<] (1 / 2 : ℝ))
          (𝓝 (2 - Real.log 5 / Real.log (13 / 8)))) ∧
    ((∀ᶠ p in 𝓝[>] (1 / 2 : ℝ), iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - 1 / 2|) (𝓝[>] (1 / 2 : ℝ))
          (𝓝 (2 - Real.log 5 / Real.log (13 / 8)))) := by
  have hright := wheatstone_cluster_number_raw_alpha_right
  have hmap : Tendsto (fun p : ℝ => 1 - p) (𝓝[<] (1 / 2 : ℝ)) (𝓝[>] (1 / 2 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun p : ℝ => 1 - p) (𝓝 (1 / 2 : ℝ)) (𝓝 (1 - (1 / 2 : ℝ))) :=
        continuousAt_const.sub continuousAt_id
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      change p < (1 / 2 : ℝ) at hp
      change (1 / 2 : ℝ) < 1 - p
      linarith
  have hinterval : ∀ᶠ p : ℝ in 𝓝[<] (1 / 2 : ℝ), p ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with p hp hp'
    change p < (1 / 2 : ℝ) at hp
    exact ⟨hp', by linarith⟩
  refine ⟨⟨?_, ?_⟩, hright⟩
  · filter_upwards [hinterval, hmap.eventually hright.1] with p hp hnonzero
    have hreflection := wheatstone_cluster_number_third_derivative_reflection p hp
    intro hzero
    rw [hzero, zero_add] at hreflection
    exact hnonzero hreflection
  · apply (hright.2.comp hmap).congr'
    filter_upwards [hinterval] with p hp
    have hreflection := wheatstone_cluster_number_third_derivative_reflection p hp
    have hthird : iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1 - p) =
        -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p := by linarith
    have hdeviation : 1 - p - 1 / 2 = -(p - 1 / 2) := by ring
    simp only [Function.comp_apply, hthird, hdeviation, abs_neg]

end
end Universality
