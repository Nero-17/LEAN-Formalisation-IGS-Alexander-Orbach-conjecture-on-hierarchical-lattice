import Universality.Percolation.ClusterNumberSmoothness
import Universality.Analysis.PolynomialRenormalizationJets
import Universality.Examples.DiamondClassical
import Universality.Examples.ClusterNumberForcing

namespace Universality
noncomputable section
open Polynomial Filter
open scoped Topology

theorem diamond_thermal_cube_lt_edges :
    deriv diamondNetwork.reliability diamondCriticalProbability ^ 3 < 4 := by
  obtain ⟨hp, hp'⟩ := diamond_critical_probability_bounds
  have hquad := diamond_critical_quadratic
  have hresponse : deriv diamondNetwork.reliability diamondCriticalProbability =
      4 - 4 * diamondCriticalProbability := by
    rw [diamond_critical_response]
    dsimp [diamondCriticalProbability]
    ring
  have hcube : (4 - 4 * diamondCriticalProbability) ^ 3 = 320 - 512 * diamondCriticalProbability := by
    have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) hquad
    nlinarith
  have hlower : (79 / 128 : ℝ) < diamondCriticalProbability := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hsq := pow_le_pow_left₀ hp.le hle 2
    norm_num at hsq
    nlinarith
  rw [hresponse, hcube]
  linarith

theorem diamond_cluster_number_critical_jets :
    deriv diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
        -3 * diamondCriticalProbability / 2 ∧
      iteratedDeriv 2 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
        3 + 3 * diamondCriticalProbability / 2 ∧
      iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
        (171 + 99 * diamondCriticalProbability) / 31 := by
  let crossing : Polynomial ℝ := 2 * X ^ 2 - X ^ 4
  let forcing : Polynomial ℝ := 2 * (1 - X) ^ 2
  obtain ⟨hp, hp'⟩ := diamond_critical_probability_bounds
  have hquad := diamond_critical_quadratic
  have hcrossing (p : ℝ) : crossing.eval p = diamondNetwork.reliability p := by
    rw [diamond_reliability]
    simp [crossing]
  have hforcing (p : ℝ) : forcing.eval p = diamondNetwork.expectedInternalClusterNumber p := by
    rw [diamond_expectedInternalClusterNumber]
    simp [forcing]
  have hfixed : crossing.eval diamondCriticalProbability = diamondCriticalProbability := by
    rw [hcrossing, diamond_critical_fixed_point]
  have hregular : ContDiffAt ℝ 3 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability :=
    diamondRule_classical.cluster_number_contDiffAt diamondCriticalProbability hp hp'
      diamond_critical_fixed_point 3 diamond_thermal_cube_lt_edges
  have hequation : (fun p => (4 : ℝ) * diamondNetwork.clusterNumberAnalyticExtension p -
      diamondNetwork.clusterNumberAnalyticExtension (crossing.eval p)) =ᶠ[𝓝 diamondCriticalProbability]
        (fun p => (3 / 2 : ℝ) * forcing.eval p) := by
    filter_upwards [Ioo_mem_nhds hp hp'] with p hinterval
    rw [hcrossing, hforcing]
    have hnext := diamondNetwork.clusterNumberAnalyticExtension_eq
      (diamondNetwork.unitReliability ⟨p, hinterval.1.le, hinterval.2.le⟩)
    change diamondNetwork.clusterNumberAnalyticExtension (diamondNetwork.reliability p) = _ at hnext
    rw [diamondNetwork.clusterNumberAnalyticExtension_eq ⟨p, hinterval.1.le, hinterval.2.le⟩, hnext]
    have heq := diamondNetwork.clusterNumberSeries_equation (by decide) ⟨p, hinterval.1.le, hinterval.2.le⟩
    norm_num at heq
    exact heq
  have hfirst := critical_first_jet_of_polynomial_renormalization
    diamondNetwork.clusterNumberAnalyticExtension crossing forcing 4 (3 / 2) diamondCriticalProbability
    hfixed (hregular.differentiableAt (by norm_num)) hequation
  have hsecond := critical_second_jet_of_polynomial_renormalization
    diamondNetwork.clusterNumberAnalyticExtension crossing forcing 4 (3 / 2) diamondCriticalProbability
    hfixed (hregular.of_le (by norm_num)) hequation
  have hthird := critical_third_jet_of_polynomial_renormalization
    diamondNetwork.clusterNumberAnalyticExtension crossing forcing 4 (3 / 2) diamondCriticalProbability
    hfixed hregular hequation
  have hcrossFirst : crossing.derivative.eval diamondCriticalProbability =
      4 - 4 * diamondCriticalProbability := by
    have hid := (crossing.hasDerivAt diamondCriticalProbability).deriv
    have heq : crossing.eval = diamondNetwork.reliability := funext hcrossing
    rw [heq, diamond_critical_response] at hid
    rw [← hid]
    dsimp [diamondCriticalProbability]
    ring
  have hcrossSecond : crossing.derivative.derivative.eval diamondCriticalProbability =
      12 * diamondCriticalProbability - 8 := by
    norm_num [crossing, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
    nlinarith
  have hcrossThird : crossing.derivative.derivative.derivative.eval diamondCriticalProbability =
      -24 * diamondCriticalProbability := by
    norm_num [crossing, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
    ring
  have hforceFirst : forcing.derivative.eval diamondCriticalProbability =
      4 * diamondCriticalProbability - 4 := by
    norm_num [forcing, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub]
    ring
  have hforceSecond : forcing.derivative.derivative.eval diamondCriticalProbability = 4 := by
    norm_num [forcing, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub]
  have hforceThird : forcing.derivative.derivative.derivative.eval diamondCriticalProbability = 0 := by
    norm_num [forcing, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub]
  rw [hcrossFirst, hforceFirst] at hfirst
  have hfirstValue : deriv diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
      -3 * diamondCriticalProbability / 2 := by
    have hid : (4 - (4 - 4 * diamondCriticalProbability)) *
        (-3 * diamondCriticalProbability / 2) = 3 / 2 * (4 * diamondCriticalProbability - 4) := by nlinarith
    have hgap : 4 - (4 - 4 * diamondCriticalProbability) ≠ 0 := by linarith
    exact (mul_left_cancel₀ hgap) (hfirst.trans hid.symm)
  have hsquare : (4 - 4 * diamondCriticalProbability) ^ 2 = 32 - 48 * diamondCriticalProbability := by nlinarith
  have hcube : (4 - 4 * diamondCriticalProbability) ^ 3 = 320 - 512 * diamondCriticalProbability := by
    have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) hquad
    nlinarith
  rw [hcrossFirst, hcrossSecond, hforceSecond, hfirstValue, hsquare] at hsecond
  have hsecondValue : iteratedDeriv 2 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
      3 + 3 * diamondCriticalProbability / 2 := by
    have hgap : 4 - (32 - 48 * diamondCriticalProbability) ≠ 0 := by
      have hs := diamondNetwork.pivotal_response_sq_lt_edges diamondCriticalProbability hp hp'
        diamond_critical_fixed_point diamondRule_classical.scale
      have hcrossDeriv := (crossing.hasDerivAt diamondCriticalProbability).deriv
      rw [show crossing.eval = diamondNetwork.reliability from funext hcrossing, hcrossFirst] at hcrossDeriv
      rw [hcrossDeriv, hsquare] at hs
      norm_num at hs
      linarith
    apply mul_left_cancel₀ hgap
    rw [hsecond]
    nlinarith
  rw [hcrossFirst, hcrossSecond, hcrossThird, hforceThird, hfirstValue, hsecondValue, hcube] at hthird
  have hthirdValue : iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability =
      (171 + 99 * diamondCriticalProbability) / 31 := by
    have hgap : 4 - (320 - 512 * diamondCriticalProbability) ≠ 0 := by
      have hc := diamond_thermal_cube_lt_edges
      have hcrossDeriv := (crossing.hasDerivAt diamondCriticalProbability).deriv
      rw [show crossing.eval = diamondNetwork.reliability from funext hcrossing, hcrossFirst] at hcrossDeriv
      rw [hcrossDeriv, hcube] at hc
      linarith
    apply mul_left_cancel₀ hgap
    rw [hthird]
    have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) hquad
    nlinarith
  exact ⟨hfirstValue, hsecondValue, hthirdValue⟩

theorem diamond_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] diamondCriticalProbability,
        iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - diamondCriticalProbability|) (𝓝[<] diamondCriticalProbability) (𝓝 (-1))) ∧
    ((∀ᶠ p in 𝓝[>] diamondCriticalProbability,
        iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension p| /
        Real.log |p - diamondCriticalProbability|) (𝓝[>] diamondCriticalProbability) (𝓝 (-1))) := by
  obtain ⟨hp, hp'⟩ := diamond_critical_probability_bounds
  have hleading : iteratedDeriv 3 diamondNetwork.clusterNumberAnalyticExtension diamondCriticalProbability ≠ 0 := by
    rw [diamond_cluster_number_critical_jets.2.2]
    positivity
  convert diamondRule_classical.cluster_number_raw_alpha_criterion diamondCriticalProbability hp hp'
    diamond_critical_fixed_point 3 (by omega) diamond_thermal_cube_lt_edges
    (by intro i hi hi'; omega) hleading using 1 <;> norm_num [diamondRule] <;> rfl

end
end Universality
