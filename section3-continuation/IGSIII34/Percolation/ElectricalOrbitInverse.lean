import IGSIII34.Percolation.ElectricalOmegaMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

theorem inverse_natural_moment_of_lintegral_bound
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value : Sample → ℝ) (measurable : Measurable value) (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (power : ℕ) (bound : ℝ≥0∞) (finite : bound ≠ ∞)
    (momentBound : (∫⁻ sample, (ENNReal.ofReal (value sample))⁻¹^power ∂measure) ≤ bound) :
    Integrable (fun sample => (value sample)⁻¹^power) measure ∧
      (∫ sample, (value sample)⁻¹^power ∂measure) ≤ bound.toReal := by
  have nonnegative : ∀ᵐ sample ∂measure, 0 ≤ (value sample)⁻¹^power :=
    positive.mono (fun _ inequality => pow_nonneg (inv_nonneg.mpr inequality.le) _)
  have equality : (∫⁻ sample, ENNReal.ofReal ((value sample)⁻¹^power) ∂measure) =
      ∫⁻ sample, (ENNReal.ofReal (value sample))⁻¹^power ∂measure := by
    apply lintegral_congr_ae
    filter_upwards [positive] with sample inequality
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr inequality.le), ENNReal.ofReal_inv_of_pos inequality]
  have realBound := equality.trans_le momentBound
  have toRealIntegrable := integrable_toReal_of_lintegral_ne_top
    (ENNReal.continuous_ofReal.measurable.comp (measurable.inv.pow_const power)).aemeasurable
    (ne_top_of_le_ne_top finite realBound)
  have integrable : Integrable (fun sample => (value sample)⁻¹^power) measure := by
    apply toRealIntegrable.congr
    filter_upwards [nonnegative] with sample inequality
    exact ENNReal.toReal_ofReal inequality
  refine ⟨integrable, ?_⟩
  have comparison := ENNReal.toReal_mono finite
    ((ofReal_integral_eq_lintegral_ofReal integrable nonnegative).trans_le realBound)
  rwa [ENNReal.toReal_ofReal (integral_nonneg_of_ae nonnegative)] at comparison

end
end IGSIII34.Probability
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem electricalOrbit_uniform_integrable_inverse_natural_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks)⁻¹^power)
        (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∫ marks, (electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks)⁻¹^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, finite, bounds⟩ := electricalOrbitLp_uniform_inverse_moment rule classical p positive belowOne fixedPoint
    growth growthPositive lowerMeans power
  refine ⟨bound.toReal, fun depth => inverse_natural_moment_of_lintegral_bound _ _
    (Lp.stronglyMeasurable _).measurable ?_ power bound finite (bounds depth)⟩
  filter_upwards [electricalOrbitLp_above_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
      growth growthPositive lowerMeans depth,
    normalizedPhysicalResistance_positive_ae rule classical p positive belowOne fixedPoint depth]
    with marks comparison physicalPositive
  have positive : (0 : ℝ) < (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by
    exact_mod_cast physicalPositive
  exact positive.trans_le comparison

theorem electricalOmega_uniform_integrable_inverse_natural_moment
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ)) (power : ℕ) :
    ∃ bound : ℝ, ∀ value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      Integrable (fun marks => (value marks)⁻¹^power) (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∫ marks, (value marks)⁻¹^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, finite, bounds⟩ := electricalOmega_uniform_inverse_moment rule classical p positive belowOne fixedPoint
    growth growthPositive lowerMeans power
  exact ⟨bound.toReal, fun value membership => inverse_natural_moment_of_lintegral_bound _ _
    (Lp.stronglyMeasurable value).measurable
    (electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive lowerMeans value membership)
    power bound finite (bounds value membership)⟩

end
end IGSIII34.Percolation
