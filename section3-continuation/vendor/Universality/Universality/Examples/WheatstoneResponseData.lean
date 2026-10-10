import Universality.Analysis.PolynomialFunctionalJets
import Universality.Examples.ClassicalSeeds
import Universality.Examples.ClusterNumberForcing
import Universality.Examples.ClusterNumberReflection

namespace Universality
noncomputable section
open Polynomial Filter Set
open scoped Topology

def wheatstoneRealCrossing : Polynomial ℝ := 2 * X ^ 2 + 2 * X ^ 3 - 5 * X ^ 4 + 2 * X ^ 5

def wheatstoneRealClusterForcing : Polynomial ℝ := 2 - 5 * X + 2 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 + X ^ 5

theorem wheatstoneRealCrossing_eval (p : ℝ) : wheatstoneRealCrossing.eval p = wheatstoneNetwork.reliability p := by
  rw [wheatstone_reliability]
  simp [wheatstoneRealCrossing]

theorem wheatstoneRealClusterForcing_eval (p : ℝ) :
    wheatstoneRealClusterForcing.eval p = wheatstoneNetwork.expectedInternalClusterNumber p := by
  rw [wheatstone_expectedInternalClusterNumber]
  simp [wheatstoneRealClusterForcing]

theorem wheatstone_real_polynomial_derivatives (p : ℝ) :
    wheatstoneRealCrossing.derivative.eval p = 4*p + 6*p^2 - 20*p^3 + 10*p^4 ∧
    wheatstoneRealCrossing.derivative.derivative.eval p = 4 + 12*p - 60*p^2 + 40*p^3 ∧
    wheatstoneRealCrossing.derivative.derivative.derivative.eval p = 12 - 120*p + 120*p^2 ∧
    wheatstoneRealClusterForcing.derivative.eval p = -5 + 4*p + 12*p^2 - 16*p^3 + 5*p^4 ∧
    wheatstoneRealClusterForcing.derivative.derivative.eval p = 4 + 24*p - 48*p^2 + 20*p^3 ∧
    wheatstoneRealClusterForcing.derivative.derivative.derivative.eval p = 24 - 96*p + 60*p^2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [wheatstoneRealCrossing, wheatstoneRealClusterForcing, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow] <;> ring

theorem wheatstone_real_derivative_eq (p : ℝ) :
    wheatstoneRealCrossing.derivative.eval p = deriv wheatstoneNetwork.reliability p := by
  have heq : wheatstoneRealCrossing.eval = wheatstoneNetwork.reliability := funext wheatstoneRealCrossing_eval
  rw [← heq]
  exact (wheatstoneRealCrossing.hasDerivAt p).deriv.symm

theorem wheatstone_real_crossing_maps_half :
    MapsTo wheatstoneRealCrossing.eval (Icc (1 / 2 : ℝ) 1) (Icc (1 / 2 : ℝ) 1) := by
  intro p hp
  change wheatstoneRealCrossing.eval p ∈ Icc (1 / 2 : ℝ) 1
  rw [wheatstoneRealCrossing_eval]
  have hupper := wheatstoneNetwork.reliability_le_one (by linarith [hp.1] : 0 ≤ p) hp.2
  refine ⟨?_, hupper⟩
  rcases hp.1.eq_or_lt with heq | hlt
  · rw [← heq]
    norm_num [wheatstone_reliability]
  exact hp.1.trans (wheatstoneNetwork.parameter_le_reliability_above_fixed (1 / 2) p
    (by norm_num) (by norm_num) (by norm_num [wheatstone_reliability]) hlt hp.2 wheatstoneRule_classical.scale)

theorem wheatstone_cluster_number_contDiffAt_three (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 3 wheatstoneNetwork.clusterNumberAnalyticExtension p := by
  apply wheatstoneRule_classical.cluster_number_contDiffAt_on_unit (1 / 2) (by norm_num) (by norm_num)
    (by change wheatstoneNetwork.reliability (1 / 2) = 1 / 2; norm_num [wheatstone_reliability]) 3 ?_ p hp
  change deriv wheatstoneNetwork.reliability (1 / 2) ^ 3 < (5 : ℝ)
  rw [wheatstone_deriv_half]
  norm_num

theorem wheatstone_cluster_number_derivative_continuousOn (order : ℕ) (horder : order ≤ 3) :
    ContinuousOn (iteratedDeriv order wheatstoneNetwork.clusterNumberAnalyticExtension) (Icc (0 : ℝ) 1) := by
  intro p hp
  have hregular : ContDiffAt ℝ order wheatstoneNetwork.clusterNumberAnalyticExtension p :=
    (wheatstone_cluster_number_contDiffAt_three p hp).of_le (by exact_mod_cast horder)
  exact (contDiffAt_iteratedDeriv_of_add wheatstoneNetwork.clusterNumberAnalyticExtension p 0 order
    (by simpa only [zero_add] using hregular)).continuousAt.continuousWithinAt

theorem wheatstone_response_polynomial_signs (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    (0 ≤ wheatstoneRealCrossing.derivative.eval p ∧ wheatstoneRealCrossing.derivative.eval p ≤ 13 / 8) ∧
    wheatstoneRealCrossing.derivative.derivative.eval p ≤ 0 ∧
    wheatstoneRealClusterForcing.derivative.eval p ≤ 0 ∧
    0 ≤ 5 + 2 * wheatstoneRealClusterForcing.derivative.eval p - wheatstoneRealCrossing.derivative.eval p ∧
    0 ≤ wheatstoneRealClusterForcing.derivative.derivative.eval p ∧
    2 * wheatstoneRealClusterForcing.derivative.derivative.derivative.eval p ≤ -18 ∧
    2 * wheatstoneRealClusterForcing.derivative.derivative.derivative.eval p -
      wheatstoneRealCrossing.derivative.derivative.derivative.eval p = -72 * (p - 1 / 2) := by
  obtain ⟨hc1, hc2, hc3, hf1, hf2, hf3⟩ := wheatstone_real_polynomial_derivatives p
  rw [hc1, hc2, hc3, hf1, hf2, hf3]
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hprod : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp.2)
  have hp2 : p^2 ≤ p := by nlinarith
  have hq0 : 0 ≤ p - 1 / 2 := sub_nonneg.mpr hp.1
  have hqHalf : p - 1 / 2 ≤ 1 / 2 := by linarith [hp.2]
  have hqProd := mul_nonneg hq0 (show 0 ≤ 1 / 2 - (p - 1 / 2) by linarith)
  have hq2 : (p - 1 / 2)^2 ≤ 1 / 4 := by nlinarith
  have hq4 := mul_nonneg (sq_nonneg (p - 1 / 2)) (sub_nonneg.mpr hq2)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hid : 4*p + 6*p^2 - 20*p^3 + 10*p^4 = 2*p*(1-p)*(2+5*p*(1-p)) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0) (sub_nonneg.mpr hp.2)) (by nlinarith)
  · have hid : 4*p + 6*p^2 - 20*p^3 + 10*p^4 =
        13 / 8 - 9*(p-1/2)^2 + 10*(p-1/2)^4 := by ring
    rw [hid]
    nlinarith [sq_nonneg (p - 1 / 2)]
  · have hid : 4 + 12*p - 60*p^2 + 40*p^3 = -2*(p-1/2)*(9-20*(p-1/2)^2) := by ring
    rw [hid]
    have hfactor : 0 ≤ 9 - 20*(p-1/2)^2 := by nlinarith
    have := mul_nonneg hq0 hfactor
    nlinarith
  · have hid : -5 + 4*p + 12*p^2 - 16*p^3 + 5*p^4 = (1-p)^2*(5*p^2-6*p-5) := by ring
    rw [hid]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith)
  · have hid : 5 + 2*(-5 + 4*p + 12*p^2 - 16*p^3 + 5*p^4) - (4*p + 6*p^2 - 20*p^3 + 10*p^4) =
        (2*p-1)*(5+6*p*(1-p)) := by ring
    rw [hid]
    exact mul_nonneg (by linarith [hp.1]) (by nlinarith)
  · have hid : 4 + 24*p - 48*p^2 + 20*p^3 = 4*(1-p)*(1+7*p-5*p^2) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.2)) (by nlinarith)
  · nlinarith
  · ring

end
end Universality
