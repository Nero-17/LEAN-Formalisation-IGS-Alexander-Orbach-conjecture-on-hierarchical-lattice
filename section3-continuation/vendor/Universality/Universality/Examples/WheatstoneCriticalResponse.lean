import Universality.Examples.WheatstoneResponseSigns

namespace Universality
noncomputable section
open Set Filter Polynomial
open scoped Topology

theorem wheatstone_cluster_number_critical_first_third :
    deriv wheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = -1 ∧
      iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) = 0 := by
  have hfirst := wheatstone_cluster_number_first_equation (1 / 2) (by norm_num)
  have hthird := wheatstone_cluster_number_third_equation (1 / 2) (by norm_num)
  norm_num [wheatstoneRealCrossing, wheatstoneRealClusterForcing, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow] at hfirst hthird
  constructor <;> nlinarith

theorem wheatstone_third_forcing_zero : wheatstoneThirdForcing (1 / 2) = 0 := by
  simp only [wheatstoneThirdForcing]
  norm_num [wheatstoneRealCrossing, wheatstoneRealClusterForcing, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow,
    wheatstone_cluster_number_critical_first_third.1]

theorem wheatstone_third_forcing_contDiffAt : ContDiffAt ℝ 1 wheatstoneThirdForcing (1 / 2) := by
  have hregular := wheatstone_cluster_number_contDiffAt_three (1 / 2) (by norm_num)
  have hfirst : ContDiffAt ℝ 1 (deriv wheatstoneNetwork.clusterNumberAnalyticExtension) (1 / 2) := by
    simpa only [iteratedDeriv_one, Nat.cast_one] using contDiffAt_iteratedDeriv_of_add
      wheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) 1 1 (hregular.of_le (by norm_num))
  have hsecond : ContDiffAt ℝ 1 (iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension) (1 / 2) :=
    contDiffAt_iteratedDeriv_of_add wheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2) 1 2 hregular
  have hfixed : wheatstoneRealCrossing.eval (1 / 2) = (1 / 2 : ℝ) := by
    norm_num [wheatstoneRealCrossing]
  have hpolynomial (polynomial : Polynomial ℝ) : ContDiffAt ℝ 1 polynomial.eval (1 / 2) :=
    ((AnalyticOnNhd.eval_polynomial polynomial) (1 / 2) (mem_univ _)).contDiffAt
  have hfirstNext : ContDiffAt ℝ 1 (deriv wheatstoneNetwork.clusterNumberAnalyticExtension)
      (wheatstoneRealCrossing.eval (1 / 2)) := by simpa only [hfixed] using hfirst
  have hsecondNext : ContDiffAt ℝ 1 (iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension)
      (wheatstoneRealCrossing.eval (1 / 2)) := by simpa only [hfixed] using hsecond
  exact ((((contDiffAt_const.mul (hpolynomial wheatstoneRealCrossing.derivative)).mul
    (hpolynomial wheatstoneRealCrossing.derivative.derivative)).mul
    (hsecondNext.comp (1 / 2 : ℝ) (hpolynomial wheatstoneRealCrossing))).add
      ((hpolynomial wheatstoneRealCrossing.derivative.derivative.derivative).mul
        (hfirstNext.comp (1 / 2 : ℝ) (hpolynomial wheatstoneRealCrossing)))).add
        (contDiffAt_const.mul (hpolynomial wheatstoneRealClusterForcing.derivative.derivative.derivative))

theorem wheatstone_third_forcing_isBigO :
    wheatstoneThirdForcing =O[𝓝 (1 / 2 : ℝ)] (fun p => p - 1 / 2) := by
  have h := (wheatstone_third_forcing_contDiffAt.differentiableAt (by norm_num)).hasDerivAt.isBigO_sub
  simpa only [wheatstone_third_forcing_zero, sub_zero] using h

end
end Universality
