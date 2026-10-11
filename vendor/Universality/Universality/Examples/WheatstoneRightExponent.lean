import Universality.Examples.WheatstonePowerResponse

namespace Universality
noncomputable section
open Set Filter
open scoped Topology

theorem wheatstone_response_right_logarithmic_order :
    Tendsto (fun p => Real.log (-iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p) /
      Real.log (p - 1 / 2)) (𝓝[>] (1 / 2 : ℝ))
        (𝓝 (Real.log 5 / Real.log (13 / 8) - 3)) := by
  have hinterval : ∀ᶠ p : ℝ in 𝓝[>] (1 / 2 : ℝ), p ∈ Ioo (1 / 2 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with p hp hp'
    exact ⟨hp, hp'⟩
  apply logarithmic_order_of_power_barriers (𝓝[>] (1 / 2 : ℝ))
    (fun p => -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p)
    (fun p => p - 1 / 2) (Real.log 5 / Real.log (13 / 8) - 3)
    wheatstone_response_order_bounds.1 wheatstone_response_order_bounds.2 ?_ ?_ ?_ ?_
  · apply (tendsto_log_abs_deviation_right (1 / 2)).congr'
    filter_upwards [hinterval] with p hp
    rw [abs_of_pos (sub_pos.mpr hp.1)]
  · filter_upwards [hinterval] with p hp
    exact ⟨sub_pos.mpr hp.1, neg_pos.mpr (wheatstone_cluster_number_third_deriv_neg p hp.1 hp.2.le)⟩
  · intro order horder horderUpper
    have hwithin : ContinuousWithinAt (fun p : ℝ =>
        -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p / (p - 1 / 2) ^ order)
        (Icc (1 / 2 : ℝ) 1) (1 / 2) :=
      (continuousWithinAt_iff_continuousAt_restrict _ (by norm_num)).mpr
        (wheatstone_half_normalized_response_continuous order horder horderUpper)
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (by norm_num : (1 / 2 : ℝ) < 1)] at hwithin
    have hsubset : Ioi (1 / 2 : ℝ) ⊆ Ici (1 / 2 : ℝ) := by
      intro p hp
      change (1 / 2 : ℝ) ≤ p
      exact le_of_lt hp
    have hright := hwithin.mono_left (nhdsWithin_mono (1 / 2 : ℝ) hsubset)
    simp only [sub_self, Real.zero_rpow horder.ne', div_zero] at hright
    filter_upwards [hinterval, hright.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp hbound
    have h := (div_le_iff₀ (Real.rpow_pos_of_pos (sub_pos.mpr hp.1) order)).mp hbound
    simpa only [one_mul] using h
  · intro order horder horderOne
    obtain ⟨bound, hbound, hlower⟩ := wheatstone_half_response_lower_power order horder horderOne
    refine ⟨bound, hbound, ?_⟩
    filter_upwards [hinterval] with p hp
    apply hlower ⟨p, hp.1.le, hp.2.le⟩
    intro heq
    have hval := congrArg Subtype.val heq
    change p = (1 / 2 : ℝ) at hval
    linarith [hp.1]

theorem wheatstone_cluster_number_raw_alpha_right :
    (∀ᶠ p in 𝓝[>] (1 / 2 : ℝ), iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - 1 / 2|) (𝓝[>] (1 / 2 : ℝ))
          (𝓝 (2 - Real.log 5 / Real.log (13 / 8))) := by
  have hinterval : ∀ᶠ p : ℝ in 𝓝[>] (1 / 2 : ℝ), p ∈ Ioo (1 / 2 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with p hp hp'
    exact ⟨hp, hp'⟩
  constructor
  · filter_upwards [hinterval] with p hp
    exact (wheatstone_cluster_number_third_deriv_neg p hp.1 hp.2.le).ne
  · have h := wheatstone_response_right_logarithmic_order.const_sub (-1)
    have hvalue : -1 - (Real.log 5 / Real.log (13 / 8) - 3) = 2 - Real.log 5 / Real.log (13 / 8) := by ring
    rw [hvalue] at h
    apply h.congr'
    filter_upwards [hinterval] with p hp
    rw [abs_of_neg (wheatstone_cluster_number_third_deriv_neg p hp.1 hp.2.le),
      abs_of_pos (sub_pos.mpr hp.1)]

end
end Universality
