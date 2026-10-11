import Universality.Examples.WheatstoneCriticalResponse
import Universality.Examples.WheatstoneHalfDynamics
import Universality.Analysis.PowerNormalizedResponse
import Universality.Examples.WheatstonePowerExponent

namespace Universality
noncomputable section
open Set Filter Polynomial
open scoped Topology

theorem wheatstone_half_polynomial_continuous (polynomial : Polynomial ℝ) :
    Continuous (fun p : Icc (1 / 2 : ℝ) 1 => polynomial.eval (p : ℝ)) :=
  (continuous_iff_continuousAt.mpr (fun p => (polynomial.hasDerivAt p).continuousAt)).comp
    continuous_subtype_val

theorem wheatstone_half_deviation_positive (p : Icc (1 / 2 : ℝ) 1) (hp : p ≠ wheatstoneHalfCenter) :
    0 < (p : ℝ) - 1 / 2 := by
  have hne : (p : ℝ) ≠ (1 / 2 : ℝ) := fun heq => hp (Subtype.ext heq)
  exact sub_pos.mpr (lt_of_le_of_ne p.property.1 hne.symm)

theorem wheatstone_half_response_continuous :
    Continuous (fun p : Icc (1 / 2 : ℝ) 1 =>
      -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hregular := wheatstone_cluster_number_contDiffAt_three p (wheatstone_half_subset_unit p.property)
  have hresponse : ContinuousAt (iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension) (p : ℝ) :=
    (contDiffAt_iteratedDeriv_of_add _ p 0 3 (by simpa only [zero_add, Nat.cast_ofNat] using hregular)).continuousAt
  exact (hresponse.comp continuous_subtype_val.continuousAt).neg

theorem wheatstone_half_response_equation (p : Icc (1 / 2 : ℝ) 1) :
    -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p =
      (wheatstoneRealCrossing.derivative.eval (p : ℝ) ^ 3 / 5) *
        (-iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (wheatstoneHalfIteration p)) +
          (-wheatstoneThirdForcing p / 5) := by
  have h := wheatstone_cluster_number_third_equation p (wheatstone_half_subset_unit p.property)
  dsimp [wheatstoneHalfIteration, wheatstoneThirdForcing]
  nlinarith

theorem wheatstone_half_normalized_forcing_continuous (order : ℝ) (horder : 0 < order) (horderOne : order < 1) :
    ContinuousAt (fun p : Icc (1 / 2 : ℝ) 1 =>
      (-wheatstoneThirdForcing p / 5) / ((p : ℝ) - 1 / 2) ^ order) wheatstoneHalfCenter := by
  have hmap : Tendsto (fun p : Icc (1 / 2 : ℝ) 1 => (p : ℝ))
      (𝓝 wheatstoneHalfCenter) (𝓝 (1 / 2 : ℝ)) := continuous_subtype_val.continuousAt.tendsto
  have hbound := wheatstone_third_forcing_isBigO.comp_tendsto hmap
  have hdeviation : Tendsto (fun p : Icc (1 / 2 : ℝ) 1 => (p : ℝ) - 1 / 2)
      (𝓝 wheatstoneHalfCenter) (𝓝 0) := by
    simpa only [sub_self] using hmap.sub_const (1 / 2)
  have hzero := normalized_forcing_tendsto_zero (𝓝 wheatstoneHalfCenter)
    (fun p => wheatstoneThirdForcing p) (fun p => (p : ℝ) - 1 / 2)
    order horderOne hbound hdeviation (Eventually.of_forall (fun p => sub_nonneg.mpr p.property.1))
  have hscaled : Tendsto (fun p : Icc (1 / 2 : ℝ) 1 =>
      (-wheatstoneThirdForcing p / 5) / ((p : ℝ) - 1 / 2) ^ order)
      (𝓝 wheatstoneHalfCenter) (𝓝 0) := by
    have h := hzero.const_mul (-1 / 5 : ℝ)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [] with p
    ring
  change Tendsto _ _ (𝓝 _)
  simpa only [wheatstoneHalfCenter, sub_self, Real.zero_rpow horder.ne', div_zero] using hscaled

theorem wheatstone_half_normalized_response_continuous (order : ℝ) (horder : 0 < order)
    (horderUpper : order < Real.log 5 / Real.log (13 / 8) - 3) :
    ContinuousAt (fun p : Icc (1 / 2 : ℝ) 1 =>
      -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p /
        ((p : ℝ) - 1 / 2) ^ order) wheatstoneHalfCenter := by
  apply continuous_power_normalized_response_of_compact_escape wheatstoneHalfIteration
    (fun p => -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p)
    (fun p => wheatstoneRealCrossing.derivative.eval (p : ℝ) ^ 3 / 5)
    (fun p => -wheatstoneThirdForcing p / 5) (fun p => (p : ℝ) - 1 / 2)
    (fun p => wheatstoneRealSecant.eval (p : ℝ)) wheatstoneHalfCenter (1 / 4) order (by norm_num) horder
    wheatstone_half_iteration_continuous.continuousAt wheatstone_half_iteration_fixed
    wheatstone_half_iteration_escape wheatstone_half_response_continuous.continuousOn
    ((continuous_subtype_val.sub continuous_const).continuousOn) (by norm_num [wheatstoneHalfCenter])
    wheatstone_half_deviation_positive
    (((wheatstone_half_polynomial_continuous wheatstoneRealCrossing.derivative).pow 3).div_const 5).continuousAt
    (wheatstone_half_polynomial_continuous wheatstoneRealSecant).continuousAt
    (fun p => wheatstone_real_secant_pos p p.property)
    (wheatstone_half_normalized_forcing_continuous order horder
      (horderUpper.trans wheatstone_response_order_bounds.2)) ?_
    (fun p => wheatstone_real_secant_identity p)
    (Eventually.of_forall wheatstone_half_response_equation)
  have hcoef := wheatstone_normalized_coefficient_lt_one order horderUpper
  have hnonneg : 0 ≤ (13 / 8 : ℝ) ^ 3 / 5 * (13 / 8 : ℝ) ^ order := by positivity
  have hvalue : wheatstoneRealCrossing.derivative.eval (wheatstoneHalfCenter : ℝ) ^ 3 / 5 *
      wheatstoneRealSecant.eval (wheatstoneHalfCenter : ℝ) ^ order =
        (13 / 8 : ℝ) ^ 3 / 5 * (13 / 8 : ℝ) ^ order := by
    norm_num [wheatstoneHalfCenter, wheatstoneRealCrossing, wheatstoneRealSecant,
      Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow]
  change |wheatstoneRealCrossing.derivative.eval (wheatstoneHalfCenter : ℝ) ^ 3 / 5 *
    wheatstoneRealSecant.eval (wheatstoneHalfCenter : ℝ) ^ order| < 1
  rw [hvalue, abs_of_nonneg hnonneg]
  exact hcoef

theorem wheatstone_half_response_lower_power (order : ℝ)
    (horder : Real.log 5 / Real.log (13 / 8) - 3 < order) (horderOne : order < 1) :
    ∃ bound > 0, ∀ p : Icc (1 / 2 : ℝ) 1, p ≠ wheatstoneHalfCenter →
      bound * ((p : ℝ) - 1 / 2) ^ order ≤
        -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p := by
  have horderPositive : 0 < order := wheatstone_response_order_bounds.1.trans horder
  have hcoefCont : ContinuousAt (fun p : Icc (1 / 2 : ℝ) 1 =>
      wheatstoneRealCrossing.derivative.eval (p : ℝ) ^ 3 / 5 * wheatstoneRealSecant.eval (p : ℝ) ^ order)
      wheatstoneHalfCenter :=
    ((((wheatstone_half_polynomial_continuous wheatstoneRealCrossing.derivative).pow 3).div_const 5).continuousAt).mul
      ((wheatstone_half_polynomial_continuous wheatstoneRealSecant).continuousAt.rpow_const (Or.inr horderPositive.le))
  have hcoefCenter : 1 < wheatstoneRealCrossing.derivative.eval (wheatstoneHalfCenter : ℝ) ^ 3 / 5 *
      wheatstoneRealSecant.eval (wheatstoneHalfCenter : ℝ) ^ order := by
    convert wheatstone_normalized_coefficient_gt_one order horder using 1 <;>
      norm_num [wheatstoneHalfCenter, wheatstoneRealCrossing, wheatstoneRealSecant,
        Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_X_pow]
  apply positive_lower_power_barrier_of_compact_escape wheatstoneHalfIteration
    (fun p => -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p)
    (fun p => wheatstoneRealCrossing.derivative.eval (p : ℝ) ^ 3 / 5)
    (fun p => -wheatstoneThirdForcing p / 5) (fun p => (p : ℝ) - 1 / 2)
    (fun p => wheatstoneRealSecant.eval (p : ℝ)) wheatstoneHalfCenter (1 / 4) order (by norm_num)
    horderPositive wheatstone_half_iteration_fixed wheatstone_half_iteration_escape
    wheatstone_half_response_continuous.continuousOn ?_ ?_
    ((continuous_subtype_val.sub continuous_const).continuousOn) (by norm_num [wheatstoneHalfCenter])
    wheatstone_half_deviation_positive (fun p => wheatstone_real_secant_pos p p.property)
    (hcoefCont.eventually (le_mem_nhds hcoefCenter)) ?_
    (fun p => wheatstone_real_secant_identity p)
    (Eventually.of_forall wheatstone_half_response_equation)
  · intro p hp
    exact neg_pos.mpr (wheatstone_cluster_number_third_deriv_neg p
      (sub_pos.mp (wheatstone_half_deviation_positive p hp)) p.property.2)
  · change 0 ≤ -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1 / 2)
    rw [wheatstone_cluster_number_critical_first_third.2]
    norm_num
  · apply Eventually.of_forall
    intro p
    have h := wheatstone_third_forcing_bound p p.property
    have hp := p.property.1
    linarith

end
end Universality
