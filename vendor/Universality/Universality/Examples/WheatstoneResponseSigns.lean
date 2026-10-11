import Universality.Analysis.CompactAffineResponse
import Universality.Examples.WheatstoneResponseEquations

namespace Universality
noncomputable section
open Set Polynomial

 theorem wheatstone_half_subset_unit : Icc (1 / 2 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
  intro p hp
  exact ⟨by linarith [hp.1], hp.2⟩

theorem wheatstone_cluster_number_first_deriv_bounds (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    -1 ≤ deriv wheatstoneNetwork.clusterNumberAnalyticExtension p ∧
      deriv wheatstoneNetwork.clusterNumberAnalyticExtension p ≤ 0 := by
  have hcontinuous : ContinuousOn (deriv wheatstoneNetwork.clusterNumberAnalyticExtension)
      (Icc (1 / 2 : ℝ) 1) := by
    simpa only [iteratedDeriv_one] using
      (wheatstone_cluster_number_derivative_continuousOn 1 (by omega)).mono wheatstone_half_subset_unit
  have hcoef (q : ℝ) (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
      0 ≤ wheatstoneRealCrossing.derivative.eval q / 5 ∧ wheatstoneRealCrossing.derivative.eval q / 5 < 1 := by
    have hsign := (wheatstone_response_polynomial_signs q hq).1
    constructor <;> linarith
  have hnegative := nonneg_of_compact_affine_renormalization (Icc (1 / 2 : ℝ) 1)
    isCompact_Icc ⟨1, by norm_num⟩ wheatstoneRealCrossing.eval
    (fun q => -deriv wheatstoneNetwork.clusterNumberAnalyticExtension q)
    (fun q => wheatstoneRealCrossing.derivative.eval q / 5)
    (fun q => -2 * wheatstoneRealClusterForcing.derivative.eval q / 5)
    wheatstone_real_crossing_maps_half hcontinuous.neg hcoef
    (by intro q hq; have hs := (wheatstone_response_polynomial_signs q hq).2.2.1; linarith)
    (by
      intro q hq
      have heq := wheatstone_cluster_number_first_equation q (wheatstone_half_subset_unit hq)
      try dsimp
      nlinarith)
  have hshifted := nonneg_of_compact_affine_renormalization (Icc (1 / 2 : ℝ) 1)
    isCompact_Icc ⟨1, by norm_num⟩ wheatstoneRealCrossing.eval
    (fun q => deriv wheatstoneNetwork.clusterNumberAnalyticExtension q + 1)
    (fun q => wheatstoneRealCrossing.derivative.eval q / 5)
    (fun q => (5 + 2 * wheatstoneRealClusterForcing.derivative.eval q - wheatstoneRealCrossing.derivative.eval q) / 5)
    wheatstone_real_crossing_maps_half (hcontinuous.add continuousOn_const) hcoef
    (by intro q hq; have hs := (wheatstone_response_polynomial_signs q hq).2.2.2.1; linarith)
    (by
      intro q hq
      have heq := wheatstone_cluster_number_first_equation q (wheatstone_half_subset_unit hq)
      try dsimp
      nlinarith)
  constructor
  · have := hshifted p hp
    linarith
  · have := hnegative p hp
    linarith

theorem wheatstone_cluster_number_second_deriv_nonneg (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    0 ≤ iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension p := by
  apply nonneg_of_compact_affine_renormalization (Icc (1 / 2 : ℝ) 1)
    isCompact_Icc ⟨1, by norm_num⟩ wheatstoneRealCrossing.eval
    (iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension)
    (fun q => wheatstoneRealCrossing.derivative.eval q ^ 2 / 5)
    (fun q => (wheatstoneRealCrossing.derivative.derivative.eval q *
      deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval q) +
        2 * wheatstoneRealClusterForcing.derivative.derivative.eval q) / 5)
    wheatstone_real_crossing_maps_half
    ((wheatstone_cluster_number_derivative_continuousOn 2 (by omega)).mono wheatstone_half_subset_unit)
    ?_ ?_ ?_ p hp
  · intro q hq
    have hs := (wheatstone_response_polynomial_signs q hq).1
    have hpow := pow_le_pow_left₀ hs.1 hs.2 2
    constructor
    · positivity
    · norm_num at hpow
      linarith
  · intro q hq
    have hs := wheatstone_response_polynomial_signs q hq
    have hd := (wheatstone_cluster_number_first_deriv_bounds _ (wheatstone_real_crossing_maps_half hq)).2
    have hterm := mul_nonneg_of_nonpos_of_nonpos hs.2.1 hd
    have hf := hs.2.2.2.2.1
    try dsimp
    linarith
  · intro q hq
    have heq := wheatstone_cluster_number_second_equation q (wheatstone_half_subset_unit hq)
    try dsimp
    nlinarith

def wheatstoneThirdForcing (p : ℝ) : ℝ :=
  3 * wheatstoneRealCrossing.derivative.eval p * wheatstoneRealCrossing.derivative.derivative.eval p *
    iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
  wheatstoneRealCrossing.derivative.derivative.derivative.eval p *
    deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
  2 * wheatstoneRealClusterForcing.derivative.derivative.derivative.eval p

theorem wheatstone_third_forcing_bound (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    wheatstoneThirdForcing p ≤ -36 * (p - 1 / 2) := by
  have hs := wheatstone_response_polynomial_signs p hp
  have hfirst := wheatstone_cluster_number_first_deriv_bounds _ (wheatstone_real_crossing_maps_half hp)
  have hsecond := wheatstone_cluster_number_second_deriv_nonneg _ (wheatstone_real_crossing_maps_half hp)
  have hterm : 3 * wheatstoneRealCrossing.derivative.eval p * wheatstoneRealCrossing.derivative.derivative.eval p *
      iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) ≤ 0 := by
    have hnonneg := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) hs.1.1) hsecond
    have hproduct := mul_nonpos_of_nonneg_of_nonpos hnonneg hs.2.1
    nlinarith
  have hforcing := hs.2.2.2.2.2.1
  have hdifference := hs.2.2.2.2.2.2
  dsimp [wheatstoneThirdForcing]
  by_cases hthird : 0 ≤ wheatstoneRealCrossing.derivative.derivative.derivative.eval p
  · have hproduct := mul_nonpos_of_nonneg_of_nonpos hthird hfirst.2
    nlinarith [hp.2]
  · have hproduct := mul_nonneg
      (show 0 ≤ deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) + 1 by linarith)
      (neg_nonneg.mpr (le_of_not_ge hthird))
    nlinarith [hp.1]

theorem wheatstone_cluster_number_third_deriv_nonpos (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ≤ 0 := by
  have hnonneg := nonneg_of_compact_affine_renormalization (Icc (1 / 2 : ℝ) 1)
    isCompact_Icc ⟨1, by norm_num⟩ wheatstoneRealCrossing.eval
    (fun q => -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension q)
    (fun q => wheatstoneRealCrossing.derivative.eval q ^ 3 / 5)
    (fun q => -wheatstoneThirdForcing q / 5)
    wheatstone_real_crossing_maps_half
    (((wheatstone_cluster_number_derivative_continuousOn 3 (by omega)).mono wheatstone_half_subset_unit).neg)
    (by
      intro q hq
      have hs := (wheatstone_response_polynomial_signs q hq).1
      have hpow := pow_le_pow_left₀ hs.1 hs.2 3
      constructor
      · exact div_nonneg (pow_nonneg hs.1 3) (by norm_num)
      · norm_num at hpow
        linarith)
    (by
      intro q hq
      have hf := wheatstone_third_forcing_bound q hq
      linarith [hq.1])
    (by
      intro q hq
      have heq := wheatstone_cluster_number_third_equation q (wheatstone_half_subset_unit hq)
      dsimp [wheatstoneThirdForcing]
      nlinarith)
  have := hnonneg p hp
  linarith

theorem wheatstone_cluster_number_third_deriv_neg (p : ℝ) (hp : 1 / 2 < p) (hp' : p ≤ 1) :
    iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p < 0 := by
  have hclosed : p ∈ Icc (1 / 2 : ℝ) 1 := ⟨hp.le, hp'⟩
  have hnext := wheatstone_cluster_number_third_deriv_nonpos _ (wheatstone_real_crossing_maps_half hclosed)
  have hcoef := (wheatstone_response_polynomial_signs p hclosed).1.1
  have hproduct := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hcoef 3) hnext
  have hforcing := wheatstone_third_forcing_bound p hclosed
  have heq := wheatstone_cluster_number_third_equation p (wheatstone_half_subset_unit hclosed)
  dsimp [wheatstoneThirdForcing] at hforcing
  nlinarith

end
end Universality
