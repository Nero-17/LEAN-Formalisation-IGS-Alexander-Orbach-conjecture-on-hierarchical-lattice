import IGSIII34.Percolation.ElectricalOrbitInverse
import IGSIII34.Probability.AllRealMoments
import IGSIII.Chemical.SmallBall.UniformMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open IGSIII.Chemical.SmallBall
open scoped ENNReal

theorem positive_natural_moment_of_lintegral_bound
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value : Sample → ℝ) (measurable : Measurable value) (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (power : ℕ) (bound : ℝ≥0∞) (finite : bound ≠ ∞)
    (momentBound : (∫⁻ sample, ENNReal.ofReal (value sample)^power ∂measure) ≤ bound) :
    Integrable (fun sample => (value sample)^power) measure ∧
      (∫ sample, (value sample)^power ∂measure) ≤ bound.toReal := by
  have equality : (∫⁻ sample, ENNReal.ofReal ((value sample)^power) ∂measure) =
      ∫⁻ sample, ENNReal.ofReal (value sample)^power ∂measure := by
    apply lintegral_congr_ae
    exact positive.mono (fun _ inequality => ENNReal.ofReal_pow inequality.le power)
  have realBound := equality.trans_le momentBound
  have toRealIntegrable := integrable_toReal_of_lintegral_ne_top
    (ENNReal.continuous_ofReal.measurable.comp (measurable.pow_const power)).aemeasurable
    (ne_top_of_le_ne_top finite realBound)
  have nonnegative := positive.mono (fun _ inequality => pow_nonneg inequality.le power)
  have integrable : Integrable (fun sample => (value sample)^power) measure :=
    toRealIntegrable.congr (nonnegative.mono (fun _ inequality => ENNReal.toReal_ofReal inequality))
  refine ⟨integrable, ?_⟩
  have comparison := ENNReal.toReal_mono finite
    ((ofReal_integral_eq_lintegral_ofReal integrable nonnegative).trans_le realBound)
  rwa [ENNReal.toReal_ofReal (integral_nonneg_of_ae nonnegative)] at comparison

theorem uniform_real_moments_of_uniform_natural_moments
    {Sample Index : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (positive : ∀ index, ∀ᵐ sample ∂measure, 0 < value index sample)
    (positiveMoments : ∀ power : ℕ, ∃ bound : ℝ, ∀ index,
      Integrable (fun sample => (value index sample)^power) measure ∧
        (∫ sample, (value index sample)^power ∂measure) ≤ bound)
    (inverseMoments : ∀ power : ℕ, ∃ bound : ℝ, ∀ index,
      Integrable (fun sample => (value index sample)⁻¹^power) measure ∧
        (∫ sample, (value index sample)⁻¹^power ∂measure) ≤ bound)
    (exponent : ℝ) : ∃ bound : ℝ, ∀ index,
      Integrable (fun sample => (value index sample)^exponent) measure ∧
        (∫ sample, (value index sample)^exponent ∂measure) ≤ bound := by
  have absoluteMeasurable (index : Index) : Measurable (fun sample => |value index sample|) := continuous_abs.measurable.comp (measurable index)
  have absoluteIntegrable (index : Index) (power : ℕ) : Integrable (fun sample => |value index sample|^power) measure :=
    ((positiveMoments power).choose_spec index).1.congr
      ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality]))
  have inverseAbsoluteIntegrable (index : Index) (power : ℕ) : Integrable (fun sample => |value index sample|⁻¹^power) measure :=
    ((inverseMoments power).choose_spec index).1.congr
      ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality]))
  by_cases exponentNonnegative : 0 ≤ exponent
  · obtain ⟨power, large⟩ := exists_nat_ge exponent
    obtain ⟨bound, bounds⟩ := positiveMoments power
    refine ⟨1+bound, fun index => ?_⟩
    have integralEquality : (∫ sample, |value index sample|^exponent ∂measure) =
        ∫ sample, (value index sample)^exponent ∂measure :=
      integral_congr_ae ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality]))
    have naturalEquality : (∫ sample, |value index sample|^power ∂measure) =
        ∫ sample, (value index sample)^power ∂measure :=
      integral_congr_ae ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality]))
    have integrable := integrable_rpow_of_nat_moments measure (absoluteMeasurable index)
      (fun sample => abs_nonneg _) (absoluteIntegrable index) exponentNonnegative
    refine ⟨integrable.congr ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality])), ?_⟩
    have comparison := integral_rpow_le_one_add_integral_pow measure (absoluteMeasurable index)
      (fun sample => abs_nonneg _) exponentNonnegative large (absoluteIntegrable index power)
    rw [integralEquality, naturalEquality] at comparison
    exact comparison.trans (add_le_add le_rfl (bounds index).2)
  · obtain ⟨power, large⟩ := exists_nat_ge (-exponent)
    obtain ⟨bound, bounds⟩ := inverseMoments power
    refine ⟨1+bound, fun index => ?_⟩
    have equality : (fun sample => (|value index sample|⁻¹)^(-exponent)) =ᵐ[measure]
        (fun sample => (value index sample)^exponent) := by
      filter_upwards [positive index] with sample inequality
      rw [abs_of_pos inequality, ← Real.rpow_neg_eq_inv_rpow, neg_neg]
    have naturalEquality : (∫ sample, |value index sample|⁻¹^power ∂measure) =
        ∫ sample, (value index sample)⁻¹^power ∂measure :=
      integral_congr_ae ((positive index).mono (fun _ inequality => by simp only [abs_of_pos inequality]))
    have integrable := integrable_rpow_of_nat_moments measure (absoluteMeasurable index).inv
      (fun sample => inv_nonneg.mpr (abs_nonneg _)) (inverseAbsoluteIntegrable index)
      (neg_nonneg.mpr (le_of_not_ge exponentNonnegative))
    refine ⟨integrable.congr equality, ?_⟩
    have comparison := integral_rpow_le_one_add_integral_pow measure (absoluteMeasurable index).inv
      (fun sample => inv_nonneg.mpr (abs_nonneg _)) (neg_nonneg.mpr (le_of_not_ge exponentNonnegative)) large
      (inverseAbsoluteIntegrable index power)
    change (∫ sample, (|value index sample|⁻¹)^(-exponent) ∂measure) ≤ 1+(∫ sample, (|value index sample|⁻¹)^power ∂measure) at comparison
    rw [integral_congr_ae equality, naturalEquality] at comparison
    exact comparison.trans (add_le_add le_rfl (bounds index).2)

end
end IGSIII34.Probability

