import IGSIII.Geometry.BoxDimensionDefinition

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Filter
open scoped Topology NNReal ENNReal

/-- Geometric packing bounds interpolate to all positive smaller radii.
The conclusion is conditional only on finiteness of the covering number at
the queried radius; infinite covering numbers already give infinite ratios. -/
theorem coveringNumber_power_lower_bound_of_geometric_packings {Space : Type*}
    [PseudoMetricSpace Space] (baseRadius contraction : ℝ≥0)
    (basePositive : 0 < baseRadius) (contractionPositive : 0 < contraction) (contractionBelowOne : contraction < 1)
    (population coefficient exponent : ℝ) (populationPositive : 0 < population) (coefficientPositive : 0 < coefficient)
    (exponentNonnegative : 0 ≤ exponent) (supercritical : 1 ≤ population * (contraction : ℝ) ^ exponent)
    (count : ℕ → ℕ)
    (packings : ∀ depth, (count depth : ENat) ≤ Metric.coveringNumber (baseRadius * contraction ^ depth) (Set.univ : Set Space))
    (countBound : ∀ depth, coefficient * population ^ depth ≤ (count depth : ℝ))
    (radius : ℝ≥0) (radiusPositive : 0 < radius) (radiusSmall : radius ≤ baseRadius)
    (finiteCover : Metric.coveringNumber radius (Set.univ : Set Space) ≠ ⊤) :
    coefficient * (baseRadius : ℝ) ^ exponent * (contraction : ℝ) ^ exponent ≤
      ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * (radius : ℝ) ^ exponent := by
  obtain ⟨depth, lower, upper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos (show 0 < (radius : ℝ) from radiusPositive) (show 0 < (baseRadius : ℝ) from basePositive))
    ((div_le_one (show 0 < (baseRadius : ℝ) from basePositive)).mpr (show (radius : ℝ) ≤ baseRadius from radiusSmall))
    (show 0 < (contraction : ℝ) from contractionPositive) (show (contraction : ℝ) < 1 from contractionBelowOne)
  have radiusUpper : radius ≤ baseRadius * contraction ^ depth := by
    change (radius : ℝ) ≤ (baseRadius : ℝ) * (contraction : ℝ) ^ depth
    simpa only [mul_comm] using (div_le_iff₀ (show 0 < (baseRadius : ℝ) from basePositive)).mp upper
  have countAtRadius := (packings depth).trans (Metric.coveringNumber_anti radiusUpper (A := (Set.univ : Set Space)))
  have numericalCount : coefficient * population ^ depth ≤
      ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) := by
    exact (countBound depth).trans (Nat.cast_le.mpr (by simpa only [ENat.toNat_coe] using ENat.toNat_le_toNat countAtRadius finiteCover))
  have radiusLower : (baseRadius : ℝ) * (contraction : ℝ) ^ (depth + 1) ≤ radius := by
    simpa only [mul_comm] using ((lt_div_iff₀ (show 0 < (baseRadius : ℝ) from basePositive)).mp lower).le
  have powerLower := Real.rpow_le_rpow (by positivity : 0 ≤ (baseRadius : ℝ) * (contraction : ℝ) ^ (depth + 1))
    radiusLower exponentNonnegative
  have supercriticalPower : 1 ≤ (population * (contraction : ℝ) ^ exponent) ^ depth := one_le_pow₀ supercritical
  calc
    _ ≤ coefficient * (baseRadius : ℝ) ^ exponent * (contraction : ℝ) ^ exponent *
        (population * (contraction : ℝ) ^ exponent) ^ depth :=
      le_mul_of_one_le_right (by positivity) supercriticalPower
    _ = (coefficient * population ^ depth) *
        ((baseRadius : ℝ) * (contraction : ℝ) ^ (depth + 1)) ^ exponent := by
      rw [Real.mul_rpow baseRadius.coe_nonneg (pow_nonneg contraction.coe_nonneg _),
        ← Real.rpow_pow_comm contraction.coe_nonneg, pow_succ, mul_pow]
      ring
    _ ≤ _ := mul_le_mul numericalCount powerLower (by positivity) (by positivity)

theorem logarithmic_ratio_ge_of_power_lower_bound (count radius coefficient exponent : ℝ)
    (countPositive : 0 < count) (radiusPositive : 0 < radius) (radiusSmall : radius < 1)
    (coefficientPositive : 0 < coefficient) (powerBound : coefficient ≤ count * radius ^ exponent) :
    exponent + Real.log coefficient / (-Real.log radius) ≤ Real.log count / (-Real.log radius) := by
  have logarithmic := Real.log_le_log coefficientPositive powerBound
  rw [Real.log_mul countPositive.ne' (Real.rpow_pos_of_pos radiusPositive exponent).ne', Real.log_rpow radiusPositive] at logarithmic
  have denominatorPositive : 0 < -Real.log radius := neg_pos.mpr (Real.log_neg radiusPositive radiusSmall)
  apply (le_div_iff₀ denominatorPositive).mpr
  rw [add_mul, div_mul_cancel₀ _ denominatorPositive.ne']
  linarith

theorem lowerBoxDimension_ge_of_covering_power_lower_bound {Space : Type*}
    [PseudoMetricSpace Space] [Nonempty Space] (exponent coefficient baseRadius : ℝ)
    (coefficientPositive : 0 < coefficient) (basePositive : 0 < baseRadius)
    (coveringBound : ∀ radius : ℝ≥0, 0 < radius → (radius : ℝ) ≤ baseRadius →
      Metric.coveringNumber radius (Set.univ : Set Space) ≠ ⊤ →
        coefficient ≤ ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * (radius : ℝ) ^ exponent) :
    (exponent : EReal) ≤ lowerBoxDimension Space := by
  have errorConvergence : Tendsto (fun radius : ℝ => Real.log coefficient / (-Real.log radius)) (𝓝[>] 0) (𝓝 0) := by
    have denominator := tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp denominator).const_mul (Real.log coefficient)
  have eventualRatio (smaller : ℝ) (strict : smaller < exponent) :
      ∀ᶠ radius : ℝ in 𝓝[>] 0, (smaller : EReal) ≤ boxCountingRatio Space radius := by
    have errorSmall := (tendsto_order.mp errorConvergence).1 (smaller - exponent) (by linarith)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < min 1 baseRadius by exact lt_min zero_lt_one basePositive)).filter_mono nhdsWithin_le_nhds,
      errorSmall] with radius radiusPositive radiusSmall errorSmall
    by_cases infiniteCover : Metric.coveringNumber radius.toNNReal (Set.univ : Set Space) = ⊤
    · simp only [boxCountingRatio, infiniteCover, ↓reduceIte, le_top]
    have countPositive : 0 < ((Metric.coveringNumber radius.toNNReal (Set.univ : Set Space)).toNat : ℝ) := by
      exact_mod_cast ENat.toNat_pos (ne_of_gt (Metric.coveringNumber_pos_iff.mpr Set.univ_nonempty)) infiniteCover
    have powerBound := coveringBound radius.toNNReal (by simpa using radiusPositive)
      (by simpa only [Real.coe_toNNReal radius radiusPositive.le] using (lt_min_iff.mp radiusSmall).2.le) infiniteCover
    have numerical := logarithmic_ratio_ge_of_power_lower_bound
      ((Metric.coveringNumber radius.toNNReal (Set.univ : Set Space)).toNat : ℝ) radius coefficient exponent
      countPositive radiusPositive (lt_min_iff.mp radiusSmall).1 coefficientPositive
      (by simpa only [Real.coe_toNNReal radius radiusPositive.le] using powerBound)
    rw [boxCountingRatio, if_neg infiniteCover]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  apply (le_liminf_iff').mpr
  intro smaller strict
  by_cases bottom : smaller = ⊥
  · subst smaller
    exact Eventually.of_forall (fun _ => bot_le)
  by_cases top : smaller = ⊤
  · simp [top] at strict
  lift smaller to ℝ using ⟨top, bottom⟩
  exact eventualRatio smaller (EReal.coe_lt_coe_iff.mp strict)

end
end IGSIII.Geometry
