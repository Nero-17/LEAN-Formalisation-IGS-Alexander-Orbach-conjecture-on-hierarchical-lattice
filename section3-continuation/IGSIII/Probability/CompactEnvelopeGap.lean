import IGSIII.Probability.Lp2Mean
import IGSIII.Probability.NormalizePositiveFixedPoint
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {Sample : Type*} [MeasurableSpace Sample] {measure : Measure Sample}

theorem scalar_nonnegative_of_positive_lp_domination [IsProbabilityMeasure measure]
    (first second : Lp ℝ 2 measure)
    (firstPositive : ∀ᵐ sample ∂measure, 0 < first sample)
    (secondPositive : ∀ᵐ sample ∂measure, 0 < second sample)
    (scalar : ℝ) (comparison : first ≤ scalar • second) : 0 ≤ scalar := by
  by_contra negative
  have scalarNegative : scalar < 0 := lt_of_not_ge negative
  have impossible : ∀ᵐ sample ∂measure, False := by
    filter_upwards [firstPositive, secondPositive, (Lp.coeFn_le _ _).mpr comparison,
      Lp.coeFn_smul scalar second] with sample firstStrict secondStrict inequality scalarEquality
    rw [scalarEquality, Pi.smul_apply, smul_eq_mul] at inequality
    exact (firstStrict.trans_le inequality).not_ge (mul_nonpos_of_nonpos_of_nonneg scalarNegative.le secondStrict.le)
  obtain ⟨_, contradiction⟩ := impossible.exists
  exact contradiction

theorem exists_least_lp_domination_scalar [IsProbabilityMeasure measure]
    (family : Set (Lp ℝ 2 measure)) (nonempty : family.Nonempty)
    (base : Lp ℝ 2 measure) (basePositive : ∀ᵐ sample ∂measure, 0 < base sample)
    (familyPositive : ∀ value ∈ family, ∀ᵐ sample ∂measure, 0 < value sample)
    (bound : ℝ) (bounded : ∀ value ∈ family, value ≤ bound • base) :
    ∃ scalar : ℝ, 0 ≤ scalar ∧
      (∀ value ∈ family, value ≤ scalar • base) ∧
      ∀ competitor : ℝ, (∀ value ∈ family, value ≤ competitor • base) → scalar ≤ competitor := by
  let admissible : Set ℝ := {scalar | ∀ value ∈ family, value ≤ scalar • base}
  have closed : IsClosed admissible := by
    dsimp only [admissible]
    simp only [setOf_forall]
    exact isClosed_iInter (fun value => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (continuous_id.smul continuous_const)))
  have admissibleNonempty : admissible.Nonempty := ⟨bound, bounded⟩
  have boundedBelow : BddBelow admissible := by
    refine ⟨0, ?_⟩
    intro scalar scalarMember
    obtain ⟨value, member⟩ := nonempty
    exact scalar_nonnegative_of_positive_lp_domination value base (familyPositive value member)
      basePositive scalar (scalarMember value member)
  have least := closed.isLeast_csInf admissibleNonempty boundedBelow
  refine ⟨sInf admissible, ?_, least.1, ?_⟩
  · obtain ⟨value, member⟩ := nonempty
    exact scalar_nonnegative_of_positive_lp_domination value base (familyPositive value member)
      basePositive _ (least.1 value member)
  · exact fun competitor member => least.2 member

theorem compact_order_gap_has_positive_mean [IsFiniteMeasure measure]
    (family : Set (Lp ℝ 2 measure)) (compact : IsCompact family)
    (upper : Lp ℝ 2 measure) (upperBound : ∀ value ∈ family, value ≤ upper)
    (absent : upper ∉ family) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ value ∈ family,
      gap ≤ ∫ sample, (upper - value) sample ∂measure := by
  have continuous : Continuous (fun value : Lp ℝ 2 measure =>
      ∫ sample, (upper - value) sample ∂measure) :=
    (lp2_mean_continuous measure).comp (continuous_const.sub continuous_id)
  apply compact.exists_forall_le' continuous.continuousOn
  intro value member
  have gapNonnegative : 0 ≤ upper - value := sub_nonneg.mpr (upperBound value member)
  have meanNonnegative := integral_nonneg_of_ae ((Lp.coeFn_nonneg _).mpr gapNonnegative)
  apply lt_of_le_of_ne meanNonnegative
  intro zeroMean
  have gapZero : upper - value = 0 := by
    apply Lp.ext
    have zeroAe := (integral_eq_zero_iff_of_nonneg_ae ((Lp.coeFn_nonneg _).mpr gapNonnegative)
      (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (upper - value)))).mp zeroMean.symm
    exact zeroAe.trans (Lp.coeFn_zero ℝ 2 measure).symm
  have equality : upper = value := sub_eq_zero.mp gapZero
  exact absent (equality ▸ member)

end IGSIII.Probability
