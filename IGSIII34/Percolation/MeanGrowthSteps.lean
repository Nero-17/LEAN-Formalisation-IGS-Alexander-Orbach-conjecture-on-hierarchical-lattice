import IGSIII34.Percolation.GenerationMean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators NNReal

theorem electricalOrbitScale_pivotal_growth
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth steps : ℕ) :
    deriv rule.network.reliability parameter^steps *
        (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) ≤
      (electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+steps) : ℝ) := by
  have derivativePositive := zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    parameter positive belowOne fixedPoint classical.scale)
  induction steps with
  | zero => simp
  | succ steps previous =>
    have outputLower := (normalizedElectricalOrbit_outputMean_bounds rule classical parameter positive belowOne fixedPoint (depth+steps)).1
    have outputNonnegative := derivativePositive.le.trans outputLower
    change _ ≤ ((Real.toNNReal _ * electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+steps) : ℝ≥0) : ℝ)
    rw [NNReal.coe_mul]
    change _ ≤ (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint (depth+steps))) : ℝ) *
        (electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+steps) : ℝ)
    rw [Real.coe_toNNReal _ outputNonnegative]
    calc
      _ = deriv rule.network.reliability parameter *
          (deriv rule.network.reliability parameter^steps *
            (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ)) := by rw [pow_succ]; ring
      _ ≤ deriv rule.network.reliability parameter *
          (electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+steps) : ℝ) :=
        mul_le_mul_of_nonneg_left previous derivativePositive.le
      _ ≤ _ := mul_le_mul_of_nonneg_right outputLower
        (electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+steps)).property

theorem generation_block_electrical_mean_ratio_decay
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ) :
    conditionalMeanResistance (rule.generation fine).network parameter /
      conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter ≤
        1 / deriv rule.network.reliability parameter^(coarse+1) := by
  have derivativePositive := zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    parameter positive belowOne fixedPoint classical.scale)
  have parentPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint (coarse+fine+1)
  have growth := electricalOrbitScale_pivotal_growth rule classical parameter positive belowOne fixedPoint (fine+1) (coarse+1)
  have index : fine+1+(coarse+1) = (coarse+fine+1)+1 := by omega
  rw [index, electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint,
    electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint] at growth
  exact (div_le_div_iff₀ parentPositive (pow_pos derivativePositive _)).mpr (by simpa only [one_mul, mul_comm] using growth)

end
end IGSIII34.Percolation
