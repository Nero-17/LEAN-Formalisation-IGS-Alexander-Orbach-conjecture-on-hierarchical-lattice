import IGSIII4.EssentialDomination

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IGSIII4
noncomputable section
open MeasureTheory Filter

/-- The essential-domination argument in Section 4. The comparison premise
is a separate analytic obligation, proved for the actual electrical transfer
before this lemma can yield the manuscript's rigidity statement. -/
theorem supersolution_rigidity_of_domination
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsProbabilityMeasure measure]
    (transfer : (Sample → ℝ) → Sample → ℝ) (growth : ℝ)
    (congruent : ∀ first second : Sample → ℝ,
      first =ᵐ[measure] second → transfer first =ᵐ[measure] transfer second)
    (homogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ value : Sample → ℝ,
      (∀ᵐ sample ∂measure, 0 ≤ value sample) →
      transfer (fun sample => scalar * value sample) =ᵐ[measure]
        fun sample => scalar * transfer value sample)
    (superadditive : ∀ first second : Sample → ℝ,
      (∀ᵐ sample ∂measure, 0 ≤ first sample) →
      (∀ᵐ sample ∂measure, 0 ≤ second sample) →
      ∀ᵐ sample ∂measure, transfer first sample + transfer second sample ≤
        transfer (fun sample => first sample + second sample) sample)
    (field : Sample → ℝ) (fieldMeasurable : Measurable field)
    (fieldIntegrable : Integrable field measure)
    (fieldPositive : ∀ᵐ sample ∂measure, 0 < field sample)
    (fieldEquation : transfer field =ᵐ[measure] fun sample => growth * field sample)
    (domination : ∀ value : Sample → ℝ, Measurable value → Integrable value measure →
      (∀ᵐ sample ∂measure, 0 ≤ value sample) → 0 < ∫ sample, value sample ∂measure →
      (∀ᵐ sample ∂measure, transfer value sample ≤ growth * value sample) →
      ∃ scalar : ℝ, 0 < scalar ∧ ∀ᵐ sample ∂measure, field sample ≤ scalar * value sample)
    (value : Sample → ℝ) (valueMeasurable : Measurable value)
    (valueIntegrable : Integrable value measure)
    (valueNonnegative : ∀ᵐ sample ∂measure, 0 ≤ value sample)
    (valueMeanPositive : 0 < ∫ sample, value sample ∂measure)
    (supersolution : ∀ᵐ sample ∂measure, transfer value sample ≤ growth * value sample) :
    ∃ scalar : ℝ, 0 < scalar ∧ value =ᵐ[measure] fun sample => scalar * field sample := by
  obtain ⟨bound, boundPositive, bounded⟩ := domination value valueMeasurable valueIntegrable
    valueNonnegative valueMeanPositive supersolution
  have valuePositive : ∀ᵐ sample ∂measure, 0 < value sample := by
    filter_upwards [fieldPositive, bounded] with sample positive inequality
    exact (mul_pos_iff_of_pos_left boundPositive).mp (positive.trans_le inequality)
  obtain ⟨scalar, scalarPositive, comparison, least⟩ :=
    exists_least_ae_domination measure field value fieldPositive valuePositive bound bounded
  let gap : Sample → ℝ := fun sample => scalar * value sample - field sample
  have gapNonnegative : ∀ᵐ sample ∂measure, 0 ≤ gap sample := by
    filter_upwards [comparison] with sample inequality
    exact sub_nonneg.mpr inequality
  have gapMeasurable : Measurable gap := (valueMeasurable.const_mul scalar).sub fieldMeasurable
  have gapIntegrable : Integrable gap measure := (valueIntegrable.const_mul scalar).sub fieldIntegrable
  have gapSupersolution : ∀ᵐ sample ∂measure, transfer gap sample ≤ growth * gap sample := by
    have identity : (fun sample => field sample + gap sample) =ᵐ[measure]
        fun sample => scalar * value sample := ae_of_all measure (fun sample => by dsimp [gap]; ring)
    filter_upwards [superadditive field gap (fieldPositive.mono (fun _ positive => positive.le)) gapNonnegative,
      congruent _ _ identity, homogeneous scalar scalarPositive.le value valueNonnegative,
      fieldEquation, supersolution] with sample additive congruence scaling eigenvalue inequality
    dsimp [gap] at additive ⊢
    rw [congruence, scaling, eigenvalue] at additive
    nlinarith [mul_le_mul_of_nonneg_left inequality scalarPositive.le]
  have gapZero : gap =ᵐ[measure] 0 := by
    by_contra nonzero
    have gapMeanPositive : 0 < ∫ sample, gap sample ∂measure := by
      apply lt_of_le_of_ne (integral_nonneg_of_ae gapNonnegative)
      intro equality
      exact nonzero ((integral_eq_zero_iff_of_nonneg_ae gapNonnegative gapIntegrable).mp equality.symm)
    obtain ⟨gapBound, gapBoundPositive, gapComparison⟩ :=
      domination gap gapMeasurable gapIntegrable gapNonnegative gapMeanPositive gapSupersolution
    have improved : ∀ᵐ sample ∂measure,
        field sample ≤ (gapBound * scalar / (gapBound + 1)) * value sample := by
      filter_upwards [gapComparison] with sample inequality
      dsimp [gap] at inequality
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (show 0 < gapBound + 1 by linarith)).mpr
      nlinarith
    have improvedLeast := least (gapBound * scalar / (gapBound + 1)) improved
    have strict : gapBound * scalar / (gapBound + 1) < scalar := by
      apply (div_lt_iff₀ (show 0 < gapBound + 1 by linarith)).mpr
      nlinarith
    exact (improvedLeast.trans_lt strict).false
  refine ⟨scalar⁻¹, inv_pos.mpr scalarPositive, ?_⟩
  filter_upwards [gapZero] with sample equality
  dsimp [gap] at equality
  change value sample = scalar⁻¹ * field sample
  have identity : scalar * value sample = field sample := sub_eq_zero.mp equality
  rw [← identity, ← mul_assoc, inv_mul_cancel₀ scalarPositive.ne', one_mul]

end
end IGSIII4
