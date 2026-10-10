import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Filter

/-- The least deterministic domination constant exists for positive random
variables once one finite deterministic bound is known. -/
theorem exists_least_ae_domination
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsProbabilityMeasure measure] (first second : Sample → ℝ)
    (firstPositive : ∀ᵐ sample ∂measure, 0 < first sample)
    (secondPositive : ∀ᵐ sample ∂measure, 0 < second sample)
    (bound : ℝ) (bounded : ∀ᵐ sample ∂measure, first sample ≤ bound * second sample) :
    ∃ scalar : ℝ, 0 < scalar ∧
      (∀ᵐ sample ∂measure, first sample ≤ scalar * second sample) ∧
      ∀ competitor : ℝ,
        (∀ᵐ sample ∂measure, first sample ≤ competitor * second sample) → scalar ≤ competitor := by
  have ratioUpper : ∀ᵐ sample ∂measure, first sample / second sample ≤ bound := by
    filter_upwards [secondPositive, bounded] with sample positive inequality
    exact (div_le_iff₀ positive).mpr inequality
  have ratioLower : ∀ᵐ sample ∂measure, 0 ≤ first sample / second sample := by
    filter_upwards [firstPositive, secondPositive] with sample firstStrict secondStrict
    exact (div_pos firstStrict secondStrict).le
  have ratioBounded : IsBoundedUnder (· ≤ ·) (ae measure)
      (fun sample => first sample / second sample) :=
    isBoundedUnder_of_eventually_le ratioUpper
  have ratioCobounded : IsCoboundedUnder (· ≤ ·) (ae measure)
      (fun sample => first sample / second sample) :=
    (isBoundedUnder_of_eventually_ge ratioLower).isCoboundedUnder_le
  have leastBound := ae_le_essSup ratioBounded
  have scalarPositive : 0 < essSup (fun sample => first sample / second sample) measure := by
    have positiveAe : ∀ᵐ sample ∂measure,
        0 < essSup (fun sample => first sample / second sample) measure := by
      filter_upwards [firstPositive, secondPositive, leastBound] with sample firstStrict secondStrict inequality
      exact (div_pos firstStrict secondStrict).trans_le inequality
    exact positiveAe.exists.choose_spec
  refine ⟨essSup (fun sample => first sample / second sample) measure, scalarPositive, ?_, ?_⟩
  · filter_upwards [secondPositive, leastBound] with sample positive inequality
    exact (div_le_iff₀ positive).mp inequality
  · intro competitor comparison
    apply essSup_le_of_ae_le competitor _ ratioCobounded
    filter_upwards [secondPositive, comparison] with sample positive inequality
    exact (div_le_iff₀ positive).mpr inequality

end
end IGSIII4
