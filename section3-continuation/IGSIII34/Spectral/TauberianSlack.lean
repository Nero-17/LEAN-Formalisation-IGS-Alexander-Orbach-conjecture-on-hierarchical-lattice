import IGSIII34.Spectral.TauberianPower
import IGSIII34.Spectral.PowerSlack
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp

/-! The exponent-slack Tauberian argument of Appendix B. -/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem eventual_heat_lower_from_unequal_powers
    (kernel : ℝ → ℝ) (coefficient upperExponent lowerExponent alpha timeBound : ℝ)
    (measurable : Measurable kernel) (coefficientNonnegative : 0 ≤ coefficient)
    (upperExponentBound : upperExponent < 1) (alphaPositive : 0 < alpha)
    (timeBoundPositive : 0 < timeBound)
    (gapPositive : alpha * (1 - lowerExponent) < 1 - upperExponent)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : ∀ parameter, 0 < parameter →
      IntegrableOn (fun time => Real.exp (-parameter * time) * kernel time) (Ioi 0))
    (heatUpper : ∀ time ∈ Ioo 0 timeBound, kernel time ≤ coefficient * time ^ (-upperExponent))
    (laplaceLower : ∀ᶠ parameter : ℝ in atTop,
      parameter ^ (lowerExponent - 1) ≤ diagonalLaplace kernel parameter) :
    ∀ᶠ time : ℝ in 𝓝[>] 0,
      (1 / 2 : ℝ) * time ^ (-(alpha * lowerExponent)) ≤ kernel time := by
  let gap := (1 - upperExponent) - alpha * (1 - lowerExponent)
  have gapPositive : 0 < gap := sub_pos.mpr gapPositive
  have powerLimit : Tendsto (fun time : ℝ => time ^ gap) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow gapPositive.ne'] using
      (Real.continuousAt_rpow_const 0 gap (Or.inr gapPositive.le)).tendsto.mono_left nhdsWithin_le_nhds
  have prefixLimit := powerLimit.const_mul (coefficient / (1 - upperExponent))
  have prefixSmall := (tendsto_order.mp (by simpa using prefixLimit)).2
    (1 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have parameterDiverges := tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos alphaPositive)
  have laplaceBound := parameterDiverges.eventually laplaceLower
  have timeSmall : ∀ᶠ time : ℝ in 𝓝[>] 0, time < timeBound :=
    (eventually_lt_nhds timeBoundPositive).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, prefixSmall, laplaceBound, timeSmall]
    with time timePositive small lower smallTime
  have parameterPositive := Real.rpow_pos_of_pos timePositive (-alpha)
  have splitBound := diagonalLaplace_split_power_le kernel coefficient upperExponent
    (time ^ (-alpha)) time measurable coefficientNonnegative upperExponentBound parameterPositive timePositive
    nonnegative decreasing (integrable _ parameterPositive)
    (fun other member => heatUpper other ⟨member.1, member.2.trans_lt smallTime⟩)
  have lowerIdentity : (time ^ (-alpha)) ^ (lowerExponent - 1) =
      time ^ (alpha * (1 - lowerExponent)) := by
    rw [← Real.rpow_mul timePositive.le]
    congr 1
    ring
  rw [lowerIdentity] at lower
  have prefixIdentity : coefficient * time ^ (1 - upperExponent) / (1 - upperExponent) =
      (coefficient / (1 - upperExponent) * time ^ gap) *
        time ^ (alpha * (1 - lowerExponent)) := by
    rw [mul_assoc, ← Real.rpow_add timePositive]
    have exponentIdentity : gap + alpha * (1 - lowerExponent) = 1 - upperExponent := by dsimp [gap]; ring
    rw [exponentIdentity]
    ring
  have prefixBound : coefficient * time ^ (1 - upperExponent) / (1 - upperExponent) ≤
      (1 / 2 : ℝ) * time ^ (alpha * (1 - lowerExponent)) := by
    rw [prefixIdentity]
    exact mul_le_mul_of_nonneg_right small.le (Real.rpow_pos_of_pos timePositive _).le
  have halfBound : (1 / 2 : ℝ) * time ^ (alpha * (1 - lowerExponent)) ≤
      kernel time / time ^ (-alpha) := by linarith
  have multiplied := (le_div_iff₀ parameterPositive).mp halfBound
  calc
    _ = ((1 / 2 : ℝ) * time ^ (alpha * (1 - lowerExponent))) * time ^ (-alpha) := by
      rw [mul_assoc, ← Real.rpow_add timePositive]
      congr 2
      ring
    _ ≤ _ := multiplied

theorem spectral_dimension_of_laplace_exponent_slack
    (kernel : ℝ → ℝ) (exponent : ℝ)
    (measurable : Measurable kernel) (exponentPositive : 0 < exponent) (exponentBound : exponent < 1)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : ∀ parameter, 0 < parameter →
      IntegrableOn (fun time => Real.exp (-parameter * time) * kernel time) (Ioi 0))
    (laplaceBounds : ∀ slack : ℝ, 0 < slack → ∀ᶠ parameter : ℝ in atTop,
      parameter ^ (exponent - 1 - slack) ≤ diagonalLaplace kernel parameter ∧
        diagonalLaplace kernel parameter ≤ parameter ^ (exponent - 1 + slack)) :
    Tendsto (fun time => -2 * Real.log (kernel time) / Real.log time)
      (𝓝[>] 0) (𝓝 (2 * exponent)) := by
  have heatUpper (slack : ℝ) (slackPositive : 0 < slack) :
      ∀ᶠ time : ℝ in 𝓝[>] 0, kernel time ≤ Real.exp 1 * time ^ (-(exponent + slack)) := by
    have pulled := tendsto_inv_nhdsGT_zero.eventually (laplaceBounds slack slackPositive)
    filter_upwards [self_mem_nhdsWithin, pulled] with time positive bounds
    have exponentIdentity : exponent - 1 + slack = (exponent + slack) - 1 := by ring
    have bound := upper_heat_from_resolvent_power kernel 1 (exponent + slack) time positive
      nonnegative decreasing (integrable time⁻¹ (inv_pos.mpr positive))
      (by simpa only [one_mul, exponentIdentity] using bounds.2)
    simpa only [mul_one] using bound
  apply spectral_dimension_of_arbitrary_power_slack kernel exponent
  · intro smaller smallerBound
    have denominatorNonzero : 1 - exponent ≠ 0 := by linarith
    have continuous : ContinuousAt
        (fun slack : ℝ => (1 - exponent - 2 * slack) / (1 - exponent + slack) * (exponent - slack)) 0 := by
      fun_prop (disch := simpa using denominatorNonzero)
    have limitingExponent : Tendsto
        (fun slack : ℝ => (1 - exponent - 2 * slack) / (1 - exponent + slack) * (exponent - slack))
        (𝓝[>] 0) (𝓝 exponent) := by
      convert continuous.tendsto.mono_left nhdsWithin_le_nhds using 1
      simp [denominatorNonzero]
    have lowerExponentAbove := (tendsto_order.mp limitingExponent).1 smaller smallerBound
    have allowedPositive : 0 < min exponent ((1 - exponent) / 2) := by
      exact lt_min exponentPositive (by linarith)
    have slackSmall : ∀ᶠ slack : ℝ in 𝓝[>] 0, slack < min exponent ((1 - exponent) / 2) :=
      (eventually_lt_nhds allowedPositive).filter_mono nhdsWithin_le_nhds
    have simultaneous : ∀ᶠ slack : ℝ in 𝓝[>] 0,
        0 < slack ∧ slack < min exponent ((1 - exponent) / 2) ∧
          smaller < (1 - exponent - 2 * slack) / (1 - exponent + slack) * (exponent - slack) := by
      filter_upwards [self_mem_nhdsWithin, slackSmall, lowerExponentAbove] with slack positive small above
      exact ⟨positive, small, above⟩
    obtain ⟨slack, slackPositive, slackSmall, above⟩ := simultaneous.exists
    let alpha := (1 - exponent - 2 * slack) / (1 - exponent + slack)
    have slackLessHalf := (lt_min_iff.mp slackSmall).2
    have alphaPositive : 0 < alpha := by
      apply div_pos <;> linarith
    have alphaIdentity : alpha * (1 - exponent + slack) = 1 - exponent - 2 * slack := by
      dsimp [alpha]
      apply div_mul_cancel₀
      linarith
    have gapPositive : alpha * (1 - (exponent - slack)) < 1 - (exponent + slack) := by
      nlinarith [alphaIdentity]
    have upperExponentBound : exponent + slack < 1 := by linarith
    obtain ⟨timeBound, timeBoundPositive, localUpper⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp (heatUpper slack slackPositive)
    have laplaceLower : ∀ᶠ parameter : ℝ in atTop,
        parameter ^ ((exponent - slack) - 1) ≤ diagonalLaplace kernel parameter := by
      filter_upwards [laplaceBounds slack slackPositive] with parameter bounds
      simpa only [show exponent - 1 - slack = (exponent - slack) - 1 by ring] using bounds.1
    have lowerBound := eventual_heat_lower_from_unequal_powers kernel (Real.exp 1)
      (exponent + slack) (exponent - slack) alpha timeBound measurable (Real.exp_pos _).le
      upperExponentBound alphaPositive timeBoundPositive gapPositive nonnegative decreasing integrable
      (fun time member => localUpper member) laplaceLower
    refine ⟨1 / 2, by norm_num, ?_⟩
    have timeSmall : ∀ᶠ time : ℝ in 𝓝[>] 0, time < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, timeSmall, lowerBound] with time positive small lower
    apply le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge positive small.le (by dsimp [alpha] at above ⊢; linarith))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)) lower
  · intro larger largerBound
    refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
    simpa only [add_sub_cancel] using heatUpper (larger - exponent) (sub_pos.mpr largerBound)

end
end IGSIII34.Spectral
