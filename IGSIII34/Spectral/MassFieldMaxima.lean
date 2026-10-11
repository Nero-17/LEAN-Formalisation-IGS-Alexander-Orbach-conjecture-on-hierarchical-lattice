import IGSIII34.Spectral.ActualMassFieldMoments
import IGSIII.Geometry.DescendantEnvelope

/-! Subexponential maxima for the actual joint mass field. Uniform positive
integer moments suffice; no inverse moments or descendant independence enter.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter
open scoped Topology ENNReal

theorem eLpNorm_le_of_nonnegative_nat_moment
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (function : Sample → ℝ) (power : ℕ) (powerPositive : 0 < power) (bound : ℝ)
    (nonnegative : ∀ᵐ sample ∂measure, 0 ≤ function sample)
    (moments : (∫⁻ sample, ENNReal.ofReal (function sample) ^ power ∂measure) ≤ ENNReal.ofReal bound) :
    eLpNorm function power measure ≤ (ENNReal.ofReal bound) ^ (1 / (power : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast powerPositive.ne') (by simp)]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  have integrandEquality : (∫⁻ sample, ‖function sample‖ₑ ^ power ∂measure) =
      (∫⁻ sample, ENNReal.ofReal (function sample) ^ power ∂measure) := by
    apply lintegral_congr_ae
    filter_upwards [nonnegative] with sample positive
    rw [Real.enorm_of_nonneg positive]
  rw [integrandEquality]
  exact ENNReal.rpow_le_rpow moments (by positivity)

theorem ae_mass_field_descendant_exponential
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) (edges : ℕ)
    (field : List (Fin edges) → OrientedState → Sample → ℝ)
    (measurable : ∀ address parent, AEStronglyMeasurable (field address parent) measure)
    (nonnegative : ∀ᵐ sample ∂measure, ∀ address parent, 0 ≤ field address parent sample)
    (moments : ∀ power : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ address parent,
      (∫⁻ sample, ENNReal.ofReal (field address parent sample) ^ power ∂measure) ≤ ENNReal.ofReal bound)
    (growth : ℝ) (growthGreaterThanOne : 1 < growth) :
    ∀ᵐ sample ∂measure, ∃ threshold : ℕ, ∀ address parent, threshold ≤ address.length →
      field address parent sample ≤ growth ^ address.length := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have largePower := (tendsto_pow_atTop_atTop_of_one_lt growthGreaterThanOne).eventually
    (eventually_gt_atTop (edges : ℝ))
  obtain ⟨power, powerPositive, momentGrowth⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and largePower).exists
  obtain ⟨bound, boundPositive, momentBounds⟩ := moments power
  have decay : (edges : ℝ≥0∞) * (ENNReal.ofReal growth)⁻¹ ^ power < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos growthPositive,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr growthPositive.le),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg edges)]
    apply ENNReal.ofReal_lt_one.mpr
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_lt_one (pow_pos growthPositive power)).mpr momentGrowth
  have individual : ∀ parent, ∀ᵐ sample ∂measure, ∃ threshold : ℕ, ∀ address,
      threshold ≤ address.length → field address parent sample ≤ growth ^ address.length := by
    intro parent
    have descendants := IGSIII.Geometry.ae_descendant_envelope_exponential edges power powerPositive
      (fun address (_ : Bool) => field address parent) (fun address _ => measurable address parent)
      ((ENNReal.ofReal bound) ^ (1 / (power : ℝ))) (ENNReal.ofReal growth)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      (ENNReal.ofReal_ne_zero_iff.mpr growthPositive) ENNReal.ofReal_ne_top
      (fun address _ => eLpNorm_le_of_nonnegative_nat_moment measure _ power powerPositive bound
        (nonnegative.mono (fun _ positive => positive address parent)) (momentBounds address parent)) decay
    filter_upwards [descendants] with sample small
    obtain ⟨threshold, bounded⟩ := eventually_atTop.mp small
    refine ⟨threshold, ?_⟩
    intro address after
    have boundAt := bounded address.length after address.get false
    rw [List.ofFn_get] at boundAt
    have absBound : |field address parent sample| < growth ^ address.length := by
      apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos growthPositive address.length)).mp
      simpa only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow growthPositive.le] using boundAt
    exact (le_abs_self _).trans absBound.le
  filter_upwards [ae_all_iff.mpr individual] with sample bounds
  choose thresholds estimates using bounds
  refine ⟨Finset.univ.sup thresholds, ?_⟩
  intro address parent after
  exact estimates parent address ((Finset.le_sup (f := thresholds) (Finset.mem_univ parent)).trans after)

end
end IGSIII34.Spectral
