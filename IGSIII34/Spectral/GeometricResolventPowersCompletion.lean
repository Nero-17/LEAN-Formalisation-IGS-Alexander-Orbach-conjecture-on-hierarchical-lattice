import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

theorem rpow_nat_power_comm_completion (clock exponent : ℝ) (clockPositive : 0 < clock) (depth : ℕ) :
    (clock ^ exponent) ^ depth = (clock ^ depth) ^ exponent := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul clockPositive.le,
    show exponent * (depth : ℝ) = (depth : ℝ) * exponent by ring,
    Real.rpow_mul clockPositive.le, Real.rpow_natCast]

theorem geometric_clock_index_large_completion
    (clock parameter : ℝ) (clockAboveOne : 1 < clock) (threshold depth : ℕ)
    (largeParameter : clock ^ threshold ≤ parameter) (nearUpper : parameter < clock ^ (depth + 1)) :
    threshold ≤ depth := by
  by_contra below
  have indexBound : depth + 1 ≤ threshold := by omega
  have ordered := pow_le_pow_right₀ clockAboveOne.le indexBound
  exact (not_le_of_gt nearUpper) (ordered.trans largeParameter)

theorem geometric_resolvent_lower_to_power_completion
    (diagonal : ℝ → ℝ) (clock exponent : ℝ) (clockAboveOne : 1 < clock)
    (exponentNonpositive : exponent ≤ 0)
    (decreasing : AntitoneOn diagonal (Set.Ici 1))
    (lower : ∀ᶠ depth : ℕ in atTop, (clock ^ exponent) ^ depth ≤ diagonal (clock ^ depth)) :
    ∃ coefficient > 0, ∀ᶠ parameter : ℝ in atTop, coefficient * parameter ^ exponent ≤ diagonal parameter := by
  have clockPositive := zero_lt_one.trans clockAboveOne
  obtain ⟨threshold, bound⟩ := eventually_atTop.mp lower
  refine ⟨clock ^ exponent, Real.rpow_pos_of_pos clockPositive exponent, ?_⟩
  filter_upwards [eventually_ge_atTop (clock ^ threshold)] with parameter large
  have parameterAtLeastOne := (one_le_pow₀ clockAboveOne.le).trans large
  obtain ⟨depth, nearLower, nearUpper⟩ := exists_nat_pow_near parameterAtLeastOne clockAboveOne
  have depthLarge := geometric_clock_index_large_completion clock parameter clockAboveOne threshold depth large nearUpper
  calc
    clock ^ exponent * parameter ^ exponent ≤ clock ^ exponent * (clock ^ depth) ^ exponent :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (pow_pos clockPositive _) nearLower exponentNonpositive)
        (Real.rpow_pos_of_pos clockPositive _).le
    _ = (clock ^ (depth + 1)) ^ exponent := by
      rw [pow_succ, Real.mul_rpow (pow_nonneg clockPositive.le _) clockPositive.le, mul_comm]
    _ = (clock ^ exponent) ^ (depth + 1) := (rpow_nat_power_comm_completion clock exponent clockPositive _).symm
    _ ≤ diagonal (clock ^ (depth + 1)) := bound _ (depthLarge.trans (Nat.le_succ depth))
    _ ≤ diagonal parameter := decreasing parameterAtLeastOne (one_le_pow₀ clockAboveOne.le) nearUpper.le

theorem geometric_resolvent_upper_to_power_completion
    (diagonal : ℝ → ℝ) (clock exponent : ℝ) (clockAboveOne : 1 < clock)
    (decreasing : AntitoneOn diagonal (Set.Ici 1))
    (upper : ∀ᶠ depth : ℕ in atTop, diagonal (clock ^ depth) ≤ (clock ^ exponent) ^ depth) :
    ∃ coefficient > 0, ∀ᶠ parameter : ℝ in atTop, diagonal parameter ≤ coefficient * parameter ^ exponent := by
  have clockPositive := zero_lt_one.trans clockAboveOne
  obtain ⟨threshold, bound⟩ := eventually_atTop.mp upper
  by_cases nonnegative : 0 ≤ exponent
  · refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop (clock ^ threshold)] with parameter large
    have parameterAtLeastOne := (one_le_pow₀ clockAboveOne.le).trans large
    obtain ⟨depth, nearLower, nearUpper⟩ := exists_nat_pow_near parameterAtLeastOne clockAboveOne
    have depthLarge := geometric_clock_index_large_completion clock parameter clockAboveOne threshold depth large nearUpper
    calc
      diagonal parameter ≤ diagonal (clock ^ depth) := decreasing (one_le_pow₀ clockAboveOne.le) parameterAtLeastOne nearLower
      _ ≤ (clock ^ exponent) ^ depth := bound _ depthLarge
      _ = (clock ^ depth) ^ exponent := rpow_nat_power_comm_completion clock exponent clockPositive depth
      _ ≤ 1 * parameter ^ exponent := by
        rw [one_mul]
        exact Real.rpow_le_rpow (pow_nonneg clockPositive.le _) nearLower nonnegative
  · refine ⟨clock ^ (-exponent), Real.rpow_pos_of_pos clockPositive _, ?_⟩
    filter_upwards [eventually_ge_atTop (clock ^ threshold)] with parameter large
    have parameterAtLeastOne := (one_le_pow₀ clockAboveOne.le).trans large
    obtain ⟨depth, nearLower, nearUpper⟩ := exists_nat_pow_near parameterAtLeastOne clockAboveOne
    have depthLarge := geometric_clock_index_large_completion clock parameter clockAboveOne threshold depth large nearUpper
    have scaleIdentity : (clock ^ depth) ^ exponent = clock ^ (-exponent) * (clock ^ (depth + 1)) ^ exponent := by
      rw [Real.rpow_neg clockPositive.le, pow_succ, Real.mul_rpow (pow_nonneg clockPositive.le _) clockPositive.le]
      field_simp [(Real.rpow_pos_of_pos clockPositive exponent).ne']
    calc
      diagonal parameter ≤ diagonal (clock ^ depth) := decreasing (one_le_pow₀ clockAboveOne.le) parameterAtLeastOne nearLower
      _ ≤ (clock ^ exponent) ^ depth := bound _ depthLarge
      _ = (clock ^ depth) ^ exponent := rpow_nat_power_comm_completion clock exponent clockPositive depth
      _ = clock ^ (-exponent) * (clock ^ (depth + 1)) ^ exponent := scaleIdentity
      _ ≤ clock ^ (-exponent) * parameter ^ exponent :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le parameterAtLeastOne) nearUpper.le (le_of_not_ge nonnegative))
          (Real.rpow_pos_of_pos clockPositive _).le

theorem clock_slack_lower_to_power_completion
    (diagonal : ℝ → ℝ) (clock resistance exponent smaller : ℝ)
    (clockAboveOne : 1 < clock) (resistancePositive : 0 < resistance)
    (exponentNonpositive : exponent ≤ 0) (smallerBound : smaller < exponent)
    (exponentIdentity : clock ^ exponent = resistance⁻¹)
    (decreasing : AntitoneOn diagonal (Set.Ici 1))
    (lower : ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth : ℕ in atTop,
      1 / (resistance ^ depth * tolerance ^ depth) ≤ diagonal (clock ^ depth)) :
    ∃ coefficient > 0, ∀ᶠ parameter : ℝ in atTop, coefficient * parameter ^ smaller ≤ diagonal parameter := by
  have clockPositive := zero_lt_one.trans clockAboveOne
  let tolerance := clock ^ (exponent - smaller)
  have toleranceAboveOne : 1 < tolerance := Real.one_lt_rpow clockAboveOne (sub_pos.mpr smallerBound)
  have scalar : (resistance * tolerance)⁻¹ = clock ^ smaller := by
    dsimp only [tolerance]
    rw [Real.rpow_sub clockPositive, exponentIdentity]
    field_simp [resistancePositive.ne', (Real.rpow_pos_of_pos clockPositive smaller).ne']
  apply geometric_resolvent_lower_to_power_completion diagonal clock smaller clockAboveOne
    (smallerBound.le.trans exponentNonpositive) decreasing
  filter_upwards [lower tolerance toleranceAboveOne] with depth bound
  have normalized : ((resistance * tolerance)^depth)⁻¹ ≤ diagonal (clock^depth) := by
    simpa only [← mul_pow, one_div] using bound
  rw [← inv_pow, scalar] at normalized
  exact normalized

theorem clock_slack_upper_to_power_completion
    (diagonal : ℝ → ℝ) (clock resistance exponent larger : ℝ)
    (clockAboveOne : 1 < clock) (resistancePositive : 0 < resistance)
    (largerBound : exponent < larger)
    (exponentIdentity : clock ^ exponent = resistance⁻¹)
    (decreasing : AntitoneOn diagonal (Set.Ici 1))
    (upper : ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth : ℕ in atTop,
      diagonal (clock ^ depth) ≤ tolerance ^ depth / resistance ^ depth) :
    ∃ coefficient > 0, ∀ᶠ parameter : ℝ in atTop, diagonal parameter ≤ coefficient * parameter ^ larger := by
  have clockPositive := zero_lt_one.trans clockAboveOne
  let tolerance := clock ^ (larger - exponent)
  have toleranceAboveOne : 1 < tolerance := Real.one_lt_rpow clockAboveOne (sub_pos.mpr largerBound)
  have scalar : tolerance / resistance = clock ^ larger := by
    dsimp only [tolerance]
    rw [Real.rpow_sub clockPositive, exponentIdentity]
    field_simp [resistancePositive.ne']
  apply geometric_resolvent_upper_to_power_completion diagonal clock larger clockAboveOne decreasing
  filter_upwards [upper tolerance toleranceAboveOne] with depth bound
  simpa only [← div_pow, scalar] using bound

end
end IGSIII34.Spectral
