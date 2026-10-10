import IGSIII.Probability.CountableLpInfimum
import IGSIII.Probability.InvariantLpIterates

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem exists_positive_fixed_point_of_countable_invariant_family
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (map : Lp ℝ 2 measure → Lp ℝ 2 measure)
    (continuous : Continuous map) (monotone : Monotone map)
    (homogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ value, map (scalar • value) = scalar • map value)
    (family : Set (Lp ℝ 2 measure)) (countable : family.Countable) (nonempty : family.Nonempty)
    (invariant : Set.MapsTo map family family) (onto : Set.SurjOn map family family)
    (constant : ℝ) (constantPositive : 0 < constant)
    (comparison : ∀ first ∈ family, ∀ second ∈ family, first ≤ constant • second)
    (positivity : ∀ value ∈ family, ∀ᵐ sample ∂measure, 0 < value sample) :
    ∃ fixed : Lp ℝ 2 measure,
      map fixed = fixed ∧ (∀ᵐ sample ∂measure, 0 < fixed sample) ∧
      ∃ base ∈ family, (constant⁻¹ * constant⁻¹) • base ≤ fixed ∧ fixed ≤ base := by
  obtain ⟨base, baseMember⟩ := nonempty
  have baseNonnegative : 0 ≤ base :=
    (Lp.coeFn_nonneg base).mp ((positivity base baseMember).mono (fun _ inequality => inequality.le))
  have lowerNonnegative : 0 ≤ constant⁻¹ • base := by
    simpa only [smul_zero] using lp_smul_mono baseNonnegative constant⁻¹ (inv_nonneg.mpr constantPositive.le)
  obtain ⟨envelope, _, _, greatestLowerBound⟩ :=
    exists_countable_set_lp2_isGLB measure family countable ⟨base, baseMember⟩
      (constant⁻¹ • base) lowerNonnegative
      (fun value member => lp_inv_smul_le_of_le_smul constant constantPositive
        (comparison base baseMember value member))
  have uniformBounds := invariant_glb_iterate_bounds map monotone homogeneous family invariant onto
    constant constantPositive comparison base baseMember envelope greatestLowerBound
  have strongLowerNonnegative : 0 ≤ (constant⁻¹ * constant⁻¹) • base := by
    simpa only [smul_zero] using lp_smul_mono baseNonnegative (constant⁻¹ * constant⁻¹)
      (mul_nonneg (inv_nonneg.mpr constantPositive.le) (inv_nonneg.mpr constantPositive.le))
  obtain ⟨fixed, convergence, lowerBound, upperBound, _, _⟩ :=
    exists_antitone_lp2_limit measure (fun depth => map^[depth] envelope)
      (antitone_iterates_of_invariant_glb map monotone family onto envelope greatestLowerBound)
      ((constant⁻¹ * constant⁻¹) • base) base strongLowerNonnegative uniformBounds
  refine ⟨fixed, fixed_of_continuous_iterate_limit map continuous envelope fixed convergence, ?_,
    base, baseMember, lowerBound, upperBound⟩
  apply lp_positive_of_positive_lower lowerBound
  filter_upwards [Lp.coeFn_smul (constant⁻¹ * constant⁻¹) base, positivity base baseMember]
    with sample scalarEquality samplePositive
  rw [scalarEquality, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (mul_pos (inv_pos.mpr constantPositive) (inv_pos.mpr constantPositive)) samplePositive

end IGSIII.Probability
