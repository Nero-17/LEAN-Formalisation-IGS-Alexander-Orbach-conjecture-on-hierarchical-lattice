import IGSIII34.Percolation.ElectricalPrefixResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

def electricalPrefixProjection (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse : ℕ) :
    Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) →L[ℝ]
      Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  conditionalLp2 (independentInnovationLaw rule p positive belowOne fixedPoint)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (coarse+1))
    ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (coarse+1))

theorem exists_electricalOrbit_geometric_prefix_residual
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) :
    ∃ bound rate : ℝ, 0 ≤ bound ∧ 0 ≤ rate ∧ rate < 1 ∧ ∀ coarse fine,
      ‖electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2)-
        electricalPrefixProjection rule p positive belowOne fixedPoint coarse
          (electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2))‖ ≤ bound*rate^coarse := by
  obtain ⟨power, powerAtLeastTwo, powerContracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ)
    (deriv rule.network.reliability p)
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)
  obtain ⟨secondMoment, secondAtLeastOne, secondBounds⟩ :=
    generation_normalizedResistance_uniform_second_moment rule classical p positive belowOne fixedPoint
  obtain ⟨inverseMoment, inverseAtLeastOne, inverseBounds⟩ :=
    generation_normalizedResistance_uniform_real_inverse_moment rule classical p positive belowOne fixedPoint power
  let ratio := (rule.edges : ℝ)^(1/power)/deriv rule.network.reliability p
  let momentConstant := 2*secondMoment*Real.sqrt secondMoment*inverseMoment^(1/power)
  have derivativePositive := zero_lt_one.trans
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)
  have ratioNonnegative : 0 ≤ ratio := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) derivativePositive.le
  have ratioBelowOne : ratio < 1 := (div_lt_one derivativePositive).mpr powerContracts
  have momentConstantNonnegative : 0 ≤ momentConstant := by
    dsimp only [momentConstant]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans secondAtLeastOne))
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (zero_le_one.trans inverseAtLeastOne) _)
  have sqrtPower (depth : ℕ) : Real.sqrt (ratio^depth) = (Real.sqrt ratio)^depth := by
    apply (Real.sqrt_eq_iff_mul_self_eq (pow_nonneg ratioNonnegative _) (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
    rw [← mul_pow, Real.mul_self_sqrt ratioNonnegative]
  refine ⟨2*constant⁻¹*Real.sqrt momentConstant*Real.sqrt ratio, Real.sqrt ratio,
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr constantPositive.le))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _), Real.sqrt_nonneg _, ?_, fun coarse fine => ?_⟩
  · simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt ratioNonnegative ratioBelowOne
  · have estimate := electricalOrbit_prefix_residual_le rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds coarse fine powerAtLeastTwo
      secondMoment inverseMoment (zero_le_one.trans secondAtLeastOne) (zero_le_one.trans inverseAtLeastOne)
      secondBounds (inverseBounds fine)
    change ‖_-_‖ ≤ 2*(constant⁻¹*Real.sqrt (momentConstant*ratio^(coarse+1))) at estimate
    apply estimate.trans_eq
    rw [Real.sqrt_mul momentConstantNonnegative, sqrtPower, pow_succ]
    ring

theorem electrical_limit_geometric_prefix_residual
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth bound rate : ℝ)
    (estimates : ∀ coarse fine,
      ‖electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2)-
        electricalPrefixProjection rule p positive belowOne fixedPoint coarse
          (electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2))‖ ≤ bound*rate^coarse)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (convergence : Tendsto (electricalOrbitLp rule p positive belowOne fixedPoint growth) atTop (𝓝 endpoint))
    (coarse : ℕ) :
    ‖endpoint-electricalPrefixProjection rule p positive belowOne fixedPoint coarse endpoint‖ ≤ bound*rate^coarse := by
  have shifted := convergence.comp (tendsto_add_atTop_nat (coarse+2))
  have projected := (electricalPrefixProjection rule p positive belowOne fixedPoint coarse).continuous.tendsto endpoint |>.comp shifted
  have norms := (shifted.sub projected).norm
  apply le_of_tendsto norms
  exact Eventually.of_forall (fun fine => by simpa only [Function.comp_def, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using estimates coarse fine)

end
end IGSIII34.Percolation

