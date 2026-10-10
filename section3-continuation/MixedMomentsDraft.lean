import IGSIII34.Probability.IIDMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

theorem ennreal_rpow_sum {Edge : Type*} (base : ℝ≥0∞)
    (nonzero : base ≠ 0) (finite : base ≠ ∞) (exponent : Edge → ℝ) (indices : Finset Edge) :
    base ^ (∑ edge ∈ indices, exponent edge) = ∏ edge ∈ indices, base ^ exponent edge := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | insert edge indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent, Finset.prod_insert absent,
        ENNReal.rpow_add _ _ nonzero finite, inductionHypothesis]

theorem sum_predecessor_orders_le_sub_two {Edge : Type*} [Fintype Edge]
    (orders : Edge → ℕ) {power : ℕ} (sumOrders : ∑ edge, orders edge = power)
    (twoPositive : 2 ≤ (Finset.univ.filter (fun edge => 0 < orders edge)).card) :
    (∑ edge, (orders edge - 1)) ≤ power - 2 := by
  classical
  have identity : (∑ edge, (orders edge - 1)) +
      (Finset.univ.filter (fun edge => 0 < orders edge)).card = power := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      (∑ edge, ((orders edge - 1) + if 0 < orders edge then 1 else 0)) =
          ∑ edge, orders edge := by
        apply Finset.sum_congr rfl
        intro edge _
        split_ifs <;> omega
      _ = power := sumOrders
  omega

theorem nonconstant_assignment_sum_predecessor_orders {Edge : Type*}
    [Fintype Edge] [DecidableEq Edge] {power : ℕ} (powerAtLeastTwo : 2 ≤ power)
    (assignment : Fin power → Edge) (nonconstant : ¬ ∃ edge, assignment = fun _ => edge) :
    (∑ edge, (Fintype.card {factor : Fin power // assignment factor = edge} - 1)) ≤ power - 2 := by
  classical
  apply sum_predecessor_orders_le_sub_two
    (fun edge => Fintype.card {factor : Fin power // assignment factor = edge})
  · simp only [Fintype.card_subtype]
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin power)) (Finset.univ : Finset Edge) assignment
  · obtain ⟨first, second, distinct⟩ : ∃ first second, assignment first ≠ assignment second := by
      by_contra failure
      push Not at failure
      exact nonconstant ⟨assignment ⟨0, by omega⟩,
        funext (fun factor => failure factor ⟨0, by omega⟩)⟩
    have firstPositive : 0 < Fintype.card {factor : Fin power // assignment factor = assignment first} :=
      Fintype.card_pos_iff.mpr ⟨⟨first, rfl⟩⟩
    have secondPositive : 0 < Fintype.card {factor : Fin power // assignment factor = assignment second} :=
      Fintype.card_pos_iff.mpr ⟨⟨second, rfl⟩⟩
    exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
      ⟨assignment first, by simp [firstPositive], assignment second, by simp [secondPositive], distinct⟩)

theorem mixed_product_moments_le_sublinear {Edge : Type*} [Fintype Edge]
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) (bound : ℝ≥0) (boundAtLeastOne : 1 ≤ bound)
    (highMomentBound : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bound)
    (orders : Edge → ℕ) (ordersBound : ∀ edge, orders edge ≤ power)
    (predecessorSum : (∑ edge, (orders edge - 1)) ≤ power - 2) :
    (∏ edge, ∫⁻ value, (value : ℝ≥0∞) ^ orders edge ∂(law : Measure ℝ≥0)) ≤
      (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have denominatorPositive : 0 < (power : ℝ) - 1 := by
    have : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have localBound (edge : Edge) :
      (∫⁻ value, (value : ℝ≥0∞) ^ orders edge ∂(law : Measure ℝ≥0)) ≤
        (bound : ℝ≥0∞) ^ (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
    by_cases zeroOrder : orders edge = 0
    · simp only [zeroOrder, pow_zero, lintegral_const, measure_univ, mul_one,
        Nat.zero_sub, Nat.cast_zero, zero_div, ENNReal.rpow_zero, le_refl]
    · have positiveOrder : 1 ≤ orders edge := Nat.one_le_iff_ne_zero.mpr zeroOrder
      have interpolation := lintegral_meanOne_moment_interpolation law meanOne powerAtLeastTwo positiveOrder (ordersBound edge)
      rw [Nat.cast_sub positiveOrder, Nat.cast_one]
      exact interpolation.trans (ENNReal.rpow_le_rpow highMomentBound
        (div_nonneg (sub_nonneg.mpr (by exact_mod_cast positiveOrder)) denominatorPositive.le))
  calc
    _ ≤ ∏ edge, (bound : ℝ≥0∞) ^ (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1)) :=
      Finset.prod_le_prod' (fun edge _ => localBound edge)
    _ = (bound : ℝ≥0∞) ^ (∑ edge, (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1))) :=
      (ennreal_rpow_sum bound (by exact_mod_cast (zero_lt_one.trans_le boundAtLeastOne).ne')
        ENNReal.coe_ne_top _ Finset.univ).symm
    _ ≤ _ := by
      apply ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast boundAtLeastOne)
      rw [← Finset.sum_div, ← Nat.cast_sum]
      exact div_le_div_of_nonneg_right (by exact_mod_cast predecessorSum) denominatorPositive.le

theorem iid_sum_power_moment_bound {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) (bound : ℝ≥0) (boundAtLeastOne : 1 ≤ bound)
    (highMomentBound : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bound) :
    (∫⁻ input : Edge → ℝ≥0, (∑ edge, (input edge : ℝ≥0∞)) ^ power
      ∂Measure.pi (fun _ : Edge => (law : Measure ℝ≥0))) ≤
      (Fintype.card Edge : ℝ≥0∞) * (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) +
        (Fintype.card Edge : ℝ≥0∞) ^ power *
          (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  classical
  have constantInjective : Function.Injective (fun edge : Edge => fun _ : Fin power => edge) := by
    intro first second equality
    exact congrFun equality ⟨0, by omega⟩
  have constants : (Finset.univ.filter fun assignment : Fin power → Edge => ∃ edge, assignment = fun _ => edge) =
      Finset.univ.image (fun edge : Edge => fun _ : Fin power => edge) := by
    ext assignment
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨edge, equality⟩
      exact ⟨edge, equality.symm⟩
    · rintro ⟨edge, equality⟩
      exact ⟨edge, equality.symm⟩
  have constantTerm (chosen : Edge) :
      (∏ edge, ∫⁻ value, (value : ℝ≥0∞) ^
        Fintype.card {factor : Fin power // (fun _ : Fin power => chosen) factor = edge}
        ∂(law : Measure ℝ≥0)) =
          ∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0) := by
    rw [Finset.prod_eq_single chosen]
    · simp
    · intro edge _ distinct
      have different : chosen ≠ edge := Ne.symm distinct
      simp [different]
    · simp
  rw [iid_lintegral_sum_power]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun assignment : Fin power → Edge => ∃ edge, assignment = fun _ => edge)]
  have pureSum : (∑ assignment ∈ Finset.univ.filter (fun assignment : Fin power → Edge =>
      ∃ edge, assignment = fun _ => edge), ∏ edge,
      ∫⁻ value, (value : ℝ≥0∞) ^ Fintype.card {factor : Fin power // assignment factor = edge}
        ∂(law : Measure ℝ≥0)) =
      (Fintype.card Edge : ℝ≥0∞) * ∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0) := by
    rw [constants, Finset.sum_image (fun first _ second _ equality => constantInjective equality)]
    simp only [constantTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [pureSum]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _assignment ∈ Finset.univ.filter (fun assignment : Fin power → Edge =>
        ¬ ∃ edge, assignment = fun _ => edge),
        (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro assignment membership
      apply mixed_product_moments_le_sublinear law meanOne powerAtLeastTwo bound boundAtLeastOne highMomentBound
      · intro edge
        simpa only [Fintype.card_fin] using
          Fintype.card_subtype_le (fun factor : Fin power => assignment factor = edge)
      · exact nonconstant_assignment_sum_predecessor_orders powerAtLeastTwo assignment
          (Finset.mem_filter.mp membership).2
    _ = ((Finset.univ.filter (fun assignment : Fin power → Edge =>
        ¬ ∃ edge, assignment = fun _ => edge)).card : ℝ≥0∞) *
        (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (Fin power → Edge) : ℝ≥0∞) *
        (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_filter_le (Finset.univ : Finset (Fin power → Edge)) _
    _ = _ := by rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

end
end IGSIII34.Probability
