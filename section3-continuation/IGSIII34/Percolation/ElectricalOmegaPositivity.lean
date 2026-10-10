import IGSIII34.Percolation.ElectricalOmega
import IGSIII34.Percolation.PhysicalInverse
import IGSIII.Chemical.SmallBall.MomentLimits
import IGSIII.Probability.Lp2Mean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open scoped _root_.Topology ENNReal NNReal

theorem electricalOrbitLp_coe_ae_actual
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    ⇑(electricalOrbitLp rule p positive belowOne fixedPoint growth depth) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => growth⁻¹^depth*electricalIteration rule marks depth []) := by
  have equality := normalizedElectricalTransferLp_iterate_ae rule p positive belowOne fixedPoint
    2 growth growthNonnegative depth
  simpa only [electricalOrbitLp, nonnegativeElectricalTransfer_iterate_actual] using equality

theorem electricalOrbitLp_above_normalizedPhysicalResistance
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) ≤
        electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks := by
  have ratioLower : 1 ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)/growth^depth :=
    (le_div_iff₀ (pow_pos growthPositive _)).mpr (by simpa only [one_mul] using lowerMeans depth)
  filter_upwards [electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le depth] with marks equality
  have factorization := congrArg (fun value : ℝ≥0 => (value : ℝ))
    (electricalIteration_eq_scale_mul_normalized rule classical p positive belowOne fixedPoint depth marks)
  change electricalIteration rule marks depth [] =
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)*
      (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) at factorization
  rw [equality, factorization]
  calc
    _ = (1 : ℝ)*(normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by ring
    _ ≤ ((electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)/growth^depth)*
        (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) :=
      mul_le_mul_of_nonneg_right ratioLower
        (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks).property
    _ = _ := by rw [inv_pow]; ring


theorem electricalOmega_ae_positive
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ))
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks := by
  obtain ⟨bound, uniformInverse⟩ := normalizedPhysicalResistance_uniform_inverse_moment
    rule classical p positive belowOne fixedPoint 1
  apply orbitClusterSet_ae_positive_of_inverse_bound
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (electricalOrbitLp rule p positive belowOne fixedPoint growth) value membership
    (ENNReal.ofReal bound) ENNReal.ofReal_ne_top
  intro depth
  have inverseIntegrable := (uniformInverse depth).1
  have inverseBound := (uniformInverse depth).2
  simp only [pow_one] at inverseIntegrable inverseBound
  calc
    _ ≤ ∫⁻ marks, (ENNReal.ofReal (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ))⁻¹
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply lintegral_mono_ae
      filter_upwards [electricalOrbitLp_above_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
        growth growthPositive lowerMeans depth] with marks inequality
      exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal inequality)
    _ = ∫⁻ marks, ENNReal.ofReal ((normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ)⁻¹)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply lintegral_congr_ae
      filter_upwards [normalizedPhysicalResistance_positive_ae rule classical p positive belowOne fixedPoint depth] with marks valuePositive
      exact (ENNReal.ofReal_inv_of_pos valuePositive).symm
    _ = ENNReal.ofReal (∫ marks, (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ)⁻¹
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) := by
      exact (ofReal_integral_eq_lintegral_ofReal inverseIntegrable
        (Filter.Eventually.of_forall (fun marks => inv_nonneg.mpr
          (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks).property))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal inverseBound

theorem electricalOrbitLp_mean
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    (∫ marks, electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)/growth^depth := by
  rw [integral_congr_ae (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthNonnegative depth),
    integral_const_mul, ← electricalOrbitScale_eq_actual_mean rule classical p positive belowOne fixedPoint]
  simp only [inv_pow, div_eq_mul_inv, mul_comm]

theorem electricalOmega_mean_atLeastOne
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ))
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    1 ≤ ∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have meanCluster := membership.continuousAt_comp
    (lp2_mean_continuous (independentInnovationLaw rule p positive belowOne fixedPoint)).continuousAt
  apply (isClosed_Ici : IsClosed (Set.Ici (1 : ℝ))).mem_of_mapClusterPt meanCluster
  apply Eventually.of_forall
  intro depth
  change 1 ≤ ∫ marks, electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks
    ∂independentInnovationLaw rule p positive belowOne fixedPoint
  rw [electricalOrbitLp_mean rule classical p positive belowOne fixedPoint growth growthPositive.le]
  exact (le_div_iff₀ (pow_pos growthPositive depth)).mpr (by simpa only [one_mul] using lowerMeans depth)

end
end IGSIII34.Percolation
