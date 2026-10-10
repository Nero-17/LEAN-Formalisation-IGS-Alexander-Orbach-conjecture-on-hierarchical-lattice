import IGSIII.Geometry.BoxDimensionInterpolation
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Filter
open scoped Topology NNReal ENNReal

/-- The logarithmic covering ratio. Infinite covering numbers have value
infinity, so no conversion of an infinite cardinal to zero enters the definition. -/
def boxCountingRatio (Space : Type*) [PseudoMetricSpace Space] (radius : ℝ) : EReal :=
  if Metric.coveringNumber radius.toNNReal (Set.univ : Set Space) = ⊤ then ⊤
  else (Real.log ((Metric.coveringNumber radius.toNNReal (Set.univ : Set Space)).toNat : ℝ) /
    (-Real.log radius) : ℝ)

def upperBoxDimension (Space : Type*) [PseudoMetricSpace Space] : EReal :=
  limsup (boxCountingRatio Space) (𝓝[>] (0 : ℝ))

def lowerBoxDimension (Space : Type*) [PseudoMetricSpace Space] : EReal :=
  liminf (boxCountingRatio Space) (𝓝[>] (0 : ℝ))

theorem logarithmic_ratio_le_of_power_bound (count radius coefficient exponent : ℝ)
    (count_positive : 0 < count) (radius_positive : 0 < radius) (radius_small : radius < 1)
    (power_bound : count * radius ^ exponent ≤ coefficient) :
    Real.log count / (-Real.log radius) ≤ exponent + Real.log coefficient / (-Real.log radius) := by
  have product_positive := mul_pos count_positive (Real.rpow_pos_of_pos radius_positive exponent)
  have logarithmic := Real.log_le_log product_positive power_bound
  rw [Real.log_mul count_positive.ne' (Real.rpow_pos_of_pos radius_positive exponent).ne',
    Real.log_rpow radius_positive] at logarithmic
  have denominator_positive : 0 < -Real.log radius := neg_pos.mpr (Real.log_neg radius_positive radius_small)
  apply (div_le_iff₀ denominator_positive).mpr
  rw [add_mul, div_mul_cancel₀ _ denominator_positive.ne']
  linarith

/-- A uniform small-radius covering power bound implies the usual upper box
dimension bound, by the logarithmic definition. -/
theorem upperBoxDimension_le_of_covering_power_bound {Space : Type*}
    [PseudoMetricSpace Space] [Nonempty Space] (exponent coefficient base_radius : ℝ)
    (base_positive : 0 < base_radius)
    (covering_bound : ∀ radius : ℝ≥0, 0 < radius → (radius : ℝ) ≤ base_radius →
      Metric.coveringNumber radius (Set.univ : Set Space) ≠ ⊤ ∧
        ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * (radius : ℝ) ^ exponent ≤ coefficient) :
    upperBoxDimension Space ≤ (exponent : EReal) := by
  have error_convergence : Tendsto (fun radius : ℝ => Real.log coefficient / (-Real.log radius))
      (𝓝[>] 0) (𝓝 0) := by
    have denominator := tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp denominator).const_mul (Real.log coefficient)
  have eventual_ratio (larger : ℝ) (strict : exponent < larger) :
      ∀ᶠ radius : ℝ in 𝓝[>] 0, boxCountingRatio Space radius ≤ (larger : EReal) := by
    have error_small := (tendsto_order.mp error_convergence).2 (larger - exponent) (sub_pos.mpr strict)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < min 1 base_radius by exact lt_min zero_lt_one base_positive)).filter_mono nhdsWithin_le_nhds,
      error_small] with radius radius_positive radius_small error_small
    have radius_positive : 0 < radius := radius_positive
    have finite_bound := covering_bound radius.toNNReal (by simpa using radius_positive)
      (by simpa only [Real.coe_toNNReal radius radius_positive.le] using (lt_min_iff.mp radius_small).2.le)
    have count_positive : 0 < ((Metric.coveringNumber radius.toNNReal (Set.univ : Set Space)).toNat : ℝ) := by
      exact_mod_cast ENat.toNat_pos (ne_of_gt (Metric.coveringNumber_pos_iff.mpr Set.univ_nonempty)) finite_bound.1
    have bound := logarithmic_ratio_le_of_power_bound
      ((Metric.coveringNumber radius.toNNReal (Set.univ : Set Space)).toNat : ℝ)
      radius coefficient exponent count_positive radius_positive (lt_min_iff.mp radius_small).1
      (by simpa only [Real.coe_toNNReal radius radius_positive.le] using finite_bound.2)
    rw [boxCountingRatio, if_neg finite_bound.1]
    exact EReal.coe_le_coe_iff.mpr (bound.trans (by linarith))
  apply (limsup_le_iff').mpr
  intro larger strict
  by_cases top : larger = ⊤
  · subst larger
    exact Eventually.of_forall (fun _ => le_top)
  by_cases bottom : larger = ⊥
  · simp [bottom] at strict
  lift larger to ℝ using ⟨top, bottom⟩
  exact eventual_ratio larger (EReal.coe_lt_coe_iff.mp strict)

end
end IGSIII.Geometry
