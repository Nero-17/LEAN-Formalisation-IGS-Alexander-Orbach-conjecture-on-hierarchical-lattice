import Universality.Examples.CentralWheatstonePolynomials
import Universality.Analysis.SymmetricPolynomialFourthJet
import Universality.Percolation.ClusterNumberUnitRegularity

namespace Universality
noncomputable section
open Polynomial Filter Set
open scoped Topology

def centralWheatstoneRealCrossing : Polynomial ℝ :=
  2 * X ^ 2 + 3 * X ^ 4 - 4 * X ^ 5 - 14 * X ^ 6 + 28 * X ^ 7 - 18 * X ^ 8 + 4 * X ^ 9

def centralWheatstoneRealClusterForcing : Polynomial ℝ :=
  4 - 9 * X + 2 * X ^ 2 + 2 * X ^ 3 + 9 * X ^ 4 - X ^ 5 -
    26 * X ^ 6 + 30 * X ^ 7 - 13 * X ^ 8 + 2 * X ^ 9

theorem centralWheatstoneRealCrossing_eval (p : ℝ) :
    centralWheatstoneRealCrossing.eval p = centralWheatstoneNetwork.reliability p := by
  rw [centralWheatstone_reliability]
  simp [centralWheatstoneRealCrossing]

theorem centralWheatstoneRealClusterForcing_eval (p : ℝ) :
    centralWheatstoneRealClusterForcing.eval p = centralWheatstoneNetwork.expectedInternalClusterNumber p := by
  rw [centralWheatstone_expectedInternalClusterNumber]
  simp [centralWheatstoneRealClusterForcing]

theorem centralWheatstone_real_polynomial_critical_jets :
    centralWheatstoneRealCrossing.derivative.eval (1 / 2) = (109 / 64 : ℝ) ∧
    centralWheatstoneRealCrossing.derivative.derivative.eval (1 / 2) = 0 ∧
    centralWheatstoneRealCrossing.derivative.derivative.derivative.eval (1 / 2) = -24 ∧
    centralWheatstoneRealCrossing.derivative.derivative.derivative.derivative.eval (1 / 2) = 0 ∧
    2 * centralWheatstoneRealClusterForcing.derivative.eval (1 / 2) = (-467 / 64 : ℝ) ∧
    2 * centralWheatstoneRealClusterForcing.derivative.derivative.eval (1 / 2) = (119 / 4 : ℝ) ∧
    2 * centralWheatstoneRealClusterForcing.derivative.derivative.derivative.eval (1 / 2) = -24 ∧
    2 * centralWheatstoneRealClusterForcing.derivative.derivative.derivative.derivative.eval (1 / 2) = -420 := by
  norm_num [centralWheatstoneRealCrossing, centralWheatstoneRealClusterForcing,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow]

theorem centralWheatstone_deriv_half :
    deriv centralWheatstoneNetwork.reliability (1 / 2) = (109 / 64 : ℝ) := by
  have heq : centralWheatstoneRealCrossing.eval = centralWheatstoneNetwork.reliability :=
    funext centralWheatstoneRealCrossing_eval
  have h := (centralWheatstoneRealCrossing.hasDerivAt (1 / 2)).deriv
  rw [heq, centralWheatstone_real_polynomial_critical_jets.1] at h
  exact h

theorem centralWheatstone_thermal_fourth_lt_edges :
    deriv centralWheatstoneNetwork.reliability (1 / 2) ^ 4 < 9 := by
  rw [centralWheatstone_deriv_half]
  norm_num

theorem centralWheatstone_cluster_number_contDiffAt_four :
    ContDiffAt ℝ 4 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) :=
  centralWheatstoneRule_classical.cluster_number_contDiffAt (1 / 2) (by norm_num) (by norm_num)
    centralWheatstone_critical_fixed_point 4 centralWheatstone_thermal_fourth_lt_edges

theorem centralWheatstone_cluster_number_critical_jets :
    deriv centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = -1 ∧
    iteratedDeriv 2 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = (17408 / 3569 : ℝ) ∧
    iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = 0 ∧
    iteratedDeriv 4 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) =
      (-72900157636608 / 35107478527 : ℝ) := by
  have hfixed : centralWheatstoneRealCrossing.eval (1 / 2) = (1 / 2 : ℝ) := by
    rw [centralWheatstoneRealCrossing_eval, centralWheatstone_critical_fixed_point]
  have hregular := centralWheatstone_cluster_number_contDiffAt_four
  have hequation : (fun p => (9 : ℝ) * centralWheatstoneNetwork.clusterNumberAnalyticExtension p -
      centralWheatstoneNetwork.clusterNumberAnalyticExtension (centralWheatstoneRealCrossing.eval p)) =ᶠ[𝓝 (1 / 2 : ℝ)]
        (fun p => (2 : ℝ) * centralWheatstoneRealClusterForcing.eval p) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)] with p hp
    rw [centralWheatstoneRealCrossing_eval, centralWheatstoneRealClusterForcing_eval]
    have h := centralWheatstoneNetwork.clusterNumberAnalyticExtension_equation (by decide) p ⟨hp.1.le, hp.2.le⟩
    norm_num at h
    exact h
  obtain ⟨hcrossFirst, hcrossSecond, hcrossThird, hcrossFourth,
    hforceFirst, hforceSecond, hforceThird, hforceFourth⟩ := centralWheatstone_real_polynomial_critical_jets
  have hfirst := critical_first_jet_of_polynomial_renormalization
    centralWheatstoneNetwork.clusterNumberAnalyticExtension centralWheatstoneRealCrossing
    centralWheatstoneRealClusterForcing 9 2 (1 / 2) hfixed
      (hregular.differentiableAt (by norm_num)) hequation
  rw [hcrossFirst, hforceFirst] at hfirst
  have hfirstValue : deriv centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = -1 := by
    linarith
  have hsecond := critical_second_jet_of_polynomial_renormalization
    centralWheatstoneNetwork.clusterNumberAnalyticExtension centralWheatstoneRealCrossing
    centralWheatstoneRealClusterForcing 9 2 (1 / 2) hfixed (hregular.of_le (by norm_num)) hequation
  rw [hcrossFirst, hcrossSecond, hforceSecond] at hsecond
  have hsecondValue : iteratedDeriv 2 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) =
      (17408 / 3569 : ℝ) := by nlinarith
  have hthird := critical_third_jet_of_polynomial_renormalization
    centralWheatstoneNetwork.clusterNumberAnalyticExtension centralWheatstoneRealCrossing
    centralWheatstoneRealClusterForcing 9 2 (1 / 2) hfixed (hregular.of_le (by norm_num)) hequation
  rw [hcrossFirst, hcrossSecond, hcrossThird, hforceThird, hfirstValue] at hthird
  have hthirdValue : iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = 0 := by
    nlinarith
  have hfourth := critical_fourth_jet_of_symmetric_polynomial_renormalization
    centralWheatstoneNetwork.clusterNumberAnalyticExtension centralWheatstoneRealCrossing
    centralWheatstoneRealClusterForcing 9 2 (1 / 2) hfixed hregular hcrossSecond hcrossFourth hthirdValue hequation
  rw [hcrossFirst, hcrossThird, hforceFourth, hsecondValue] at hfourth
  refine ⟨hfirstValue, hsecondValue, hthirdValue, ?_⟩
  nlinarith

theorem centralWheatstone_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] (1 / 2 : ℝ), iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - 1 / 2|) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (-2))) ∧
    ((∀ᶠ p in 𝓝[>] (1 / 2 : ℝ), iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 centralWheatstoneNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - 1 / 2|) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (-2))) := by
  have hleading : iteratedDeriv 4 centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) ≠ 0 := by
    rw [centralWheatstone_cluster_number_critical_jets.2.2.2]
    norm_num
  have hvanish : ∀ i : ℕ, 3 ≤ i → i < 4 →
      iteratedDeriv i centralWheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = 0 := by
    intro i hi hi'
    have heq : i = 3 := by omega
    subst i
    exact centralWheatstone_cluster_number_critical_jets.2.2.1
  convert centralWheatstoneRule_classical.cluster_number_raw_alpha_criterion (1 / 2) (by norm_num) (by norm_num)
    centralWheatstone_critical_fixed_point 4 (by omega) centralWheatstone_thermal_fourth_lt_edges
    hvanish hleading using 1 <;> norm_num [centralWheatstoneRule] <;> rfl

end
end Universality
