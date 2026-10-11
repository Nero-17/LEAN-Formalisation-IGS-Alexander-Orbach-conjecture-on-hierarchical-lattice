import Universality.Examples.WheatstoneResponseData

namespace Universality
noncomputable section
open Set Polynomial

theorem wheatstone_real_crossing_maps_unit :
    MapsTo wheatstoneRealCrossing.eval (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  intro p hp
  change wheatstoneRealCrossing.eval p ∈ Icc (0 : ℝ) 1
  rw [wheatstoneRealCrossing_eval]
  exact (wheatstoneNetwork.unitReliability ⟨p, hp⟩).property

theorem wheatstone_cluster_number_closed_polynomial_jet (order : ℕ) (horder : order ≤ 3)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    iteratedDeriv order (fun q => 5 * wheatstoneNetwork.clusterNumberAnalyticExtension q -
      wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval q)) p =
        2 * (Polynomial.derivative^[order] wheatstoneRealClusterForcing).eval p := by
  apply closed_polynomial_functional_jet order wheatstoneNetwork.clusterNumberAnalyticExtension
    wheatstoneRealCrossing wheatstoneRealClusterForcing 5 2 wheatstone_real_crossing_maps_unit
    (fun q hq => (wheatstone_cluster_number_contDiffAt_three q hq).of_le (by exact_mod_cast horder)) ?_ p hp
  intro q hq
  change 5 * wheatstoneNetwork.clusterNumberAnalyticExtension q -
    wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval q) =
      2 * wheatstoneRealClusterForcing.eval q
  rw [wheatstoneRealCrossing_eval, wheatstoneRealClusterForcing_eval]
  have heq := wheatstoneNetwork.clusterNumberAnalyticExtension_equation (by decide) q hq
  norm_num at heq
  exact heq

theorem wheatstone_cluster_number_first_equation (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    5 * deriv wheatstoneNetwork.clusterNumberAnalyticExtension p =
      wheatstoneRealCrossing.derivative.eval p *
        deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          2 * wheatstoneRealClusterForcing.derivative.eval p := by
  apply first_jet_of_polynomial_equation _ _ _ 5 2 p
    ((wheatstone_cluster_number_contDiffAt_three p hp).differentiableAt (by norm_num))
      ((wheatstone_cluster_number_contDiffAt_three _ (wheatstone_real_crossing_maps_unit hp)).differentiableAt (by norm_num))
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    wheatstone_cluster_number_closed_polynomial_jet 1 (by omega) p hp

theorem wheatstone_cluster_number_second_equation (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    5 * iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension p =
      wheatstoneRealCrossing.derivative.eval p ^ 2 *
        iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          wheatstoneRealCrossing.derivative.derivative.eval p *
            deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          2 * wheatstoneRealClusterForcing.derivative.derivative.eval p := by
  apply second_jet_of_polynomial_equation _ _ _ 5 2 p
    ((wheatstone_cluster_number_contDiffAt_three p hp).of_le (by norm_num))
      ((wheatstone_cluster_number_contDiffAt_three _ (wheatstone_real_crossing_maps_unit hp)).of_le (by norm_num))
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    wheatstone_cluster_number_closed_polynomial_jet 2 (by omega) p hp

theorem wheatstone_cluster_number_third_equation (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    5 * iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p =
      wheatstoneRealCrossing.derivative.eval p ^ 3 *
        iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          3 * wheatstoneRealCrossing.derivative.eval p * wheatstoneRealCrossing.derivative.derivative.eval p *
            iteratedDeriv 2 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          wheatstoneRealCrossing.derivative.derivative.derivative.eval p *
            deriv wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneRealCrossing.eval p) +
          2 * wheatstoneRealClusterForcing.derivative.derivative.derivative.eval p := by
  apply third_jet_of_polynomial_equation _ _ _ 5 2 p
    (wheatstone_cluster_number_contDiffAt_three p hp)
      (wheatstone_cluster_number_contDiffAt_three _ (wheatstone_real_crossing_maps_unit hp))
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    wheatstone_cluster_number_closed_polynomial_jet 3 (by omega) p hp

end
end Universality
