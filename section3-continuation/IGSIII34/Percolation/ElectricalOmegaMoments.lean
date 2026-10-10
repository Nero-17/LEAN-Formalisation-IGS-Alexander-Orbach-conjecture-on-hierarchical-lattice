import IGSIII34.Percolation.ElectricalOmegaPositivity
import IGSIII.Probability.PositiveSandwichMoments

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open scoped ENNReal NNReal

theorem electricalOrbitLp_below_scaled_normalizedPhysicalResistance
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ) (growthPositive : 0 < growth)
    (upperMeans : ∀ depth, (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks ≤
        constant⁻¹*(normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by
  have ratioUpper := (div_le_iff₀ (pow_pos growthPositive depth)).mpr (upperMeans depth)
  filter_upwards [electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le depth] with marks equality
  have factorization := congrArg (fun value : ℝ≥0 => (value : ℝ))
    (electricalIteration_eq_scale_mul_normalized rule classical p positive belowOne fixedPoint depth marks)
  change electricalIteration rule marks depth [] =
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)*
      (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) at factorization
  rw [equality, factorization]
  calc
    _ = ((electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)/growth^depth)*
        (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by rw [inv_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ratioUpper
      (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks).property

theorem electricalOrbitLp_uniform_positive_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (upperMeans : ∀ depth, (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) (power : ℕ) :
    ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧ ∀ depth,
      (∫⁻ marks, ENNReal.ofReal (electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks)^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, bounds⟩ := normalizedPhysicalResistance_uniform_moment rule classical p positive belowOne fixedPoint power
  refine ⟨(ENNReal.ofReal constant⁻¹)^power*(bound : ℝ≥0∞),
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.coe_ne_top), fun depth => ?_⟩
  have comparison := lintegral_positive_power_le_of_sandwich
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (electricalOrbitLp rule p positive belowOne fixedPoint growth depth)
    (fun marks => (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ))
    constant⁻¹ (inv_nonneg.mpr constantPositive.le)
    (electricalOrbitLp_below_scaled_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
      constant growth growthPositive upperMeans depth) power
  simp only [ENNReal.ofReal_coe_nnreal] at comparison
  exact comparison.trans (mul_le_mul_left' (bounds depth) _)

theorem electricalOrbitLp_uniform_inverse_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)) (power : ℕ) :
    ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧ ∀ depth,
      (∫⁻ marks, (ENNReal.ofReal (electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks))⁻¹^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, uniformInverse⟩ := normalizedPhysicalResistance_uniform_inverse_moment
    rule classical p positive belowOne fixedPoint power
  refine ⟨ENNReal.ofReal bound, ENNReal.ofReal_ne_top, fun depth => ?_⟩
  calc
    _ ≤ ∫⁻ marks, (ENNReal.ofReal (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ))⁻¹^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply lintegral_mono_ae
      filter_upwards [electricalOrbitLp_above_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
        growth growthPositive lowerMeans depth] with marks inequality
      exact pow_le_pow_left' (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal inequality)) power
    _ = ∫⁻ marks, ENNReal.ofReal ((normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ)⁻¹^power)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply lintegral_congr_ae
      filter_upwards [normalizedPhysicalResistance_positive_ae rule classical p positive belowOne fixedPoint depth] with marks valuePositive
      have realPositive : (0 : ℝ) < (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by
        exact_mod_cast valuePositive
      rw [ENNReal.ofReal_pow (inv_nonneg.mpr realPositive.le), ENNReal.ofReal_inv_of_pos realPositive]
    _ = ENNReal.ofReal (∫ marks, (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ)⁻¹^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) := by
      exact (ofReal_integral_eq_lintegral_ofReal (uniformInverse depth).1
        (Filter.Eventually.of_forall (fun marks => pow_nonneg (inv_nonneg.mpr
          (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks).property) power))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (uniformInverse depth).2

theorem electricalOmega_uniform_positive_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (upperMeans : ∀ depth, (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) (power : ℕ) :
    ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧ ∀ value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      (∫⁻ marks, ENNReal.ofReal (value marks)^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, finiteBound, bounds⟩ := electricalOrbitLp_uniform_positive_moment rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive upperMeans power
  refine ⟨bound, finiteBound, fun value membership => ?_⟩
  exact orbitClusterSet_lintegral_continuous_response_le (independentInnovationLaw rule p positive belowOne fixedPoint)
    (electricalOrbitLp rule p positive belowOne fixedPoint growth) value membership
    (fun value => ENNReal.ofReal value^power) ((ENNReal.continuous_pow power).comp ENNReal.continuous_ofReal) bound bounds

theorem electricalOmega_uniform_inverse_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)) (power : ℕ) :
    ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧ ∀ value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      (∫⁻ marks, (ENNReal.ofReal (value marks))⁻¹^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, finiteBound, bounds⟩ := electricalOrbitLp_uniform_inverse_moment rule classical p positive belowOne fixedPoint
    growth growthPositive lowerMeans power
  refine ⟨bound, finiteBound, fun value membership => ?_⟩
  exact orbitClusterSet_lintegral_continuous_response_le (independentInnovationLaw rule p positive belowOne fixedPoint)
    (electricalOrbitLp rule p positive belowOne fixedPoint growth) value membership
    (fun value => (ENNReal.ofReal value)⁻¹^power)
    ((ENNReal.continuous_pow power).comp ENNReal.continuous_ofReal.fun_inv) bound bounds

end
end IGSIII34.Percolation
