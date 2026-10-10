import Universality.Probability.FiniteProductMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Logic.Equiv.Prod
import IGSIII.Chemical.PathBounds
import Universality.Percolation.ProductDisintegration

/-! Positive-moment estimates for normalized finite laws.  These are analytic
steps used with the explicit selected-path product law, not assumptions of a
stationary law or of uniform moments. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {Outcome : Type*} [Fintype Outcome]

theorem finite_mean_one_moment_interpolation (weight value : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome)
    (meanOne : ∑ outcome, weight outcome * value outcome = 1)
    {power order : ℕ} (powerAtLeastTwo : 2 ≤ power) (orderPositive : 1 ≤ order)
    (orderBound : order ≤ power) :
    (∑ outcome, weight outcome * value outcome ^ order) ≤
      (∑ outcome, weight outcome * value outcome ^ power) ^
        (((order : ℝ) - 1) / ((power : ℝ) - 1)) := by
  have denominatorPositive : 0 < (power : ℝ) - 1 := by
    have powerBound : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have orderAtLeastOne : (1 : ℝ) ≤ order := by exact_mod_cast orderPositive
  have orderAtMostPower : (order : ℝ) ≤ power := by exact_mod_cast orderBound
  have exponentNonnegative : 0 ≤ ((order : ℝ) - 1) / ((power : ℝ) - 1) :=
    div_nonneg (sub_nonneg.mpr orderAtLeastOne) denominatorPositive.le
  have exponentAtMostOne : ((order : ℝ) - 1) / ((power : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ denominatorPositive).mpr
    linarith
  have interpolation := (Real.concaveOn_rpow exponentNonnegative exponentAtMostOne).le_map_sum
    (t := Finset.univ) (w := fun outcome => weight outcome * value outcome)
    (p := fun outcome => value outcome ^ (power - 1))
    (fun outcome _ => mul_nonneg (weightNonnegative outcome) (valueNonnegative outcome))
    meanOne (fun outcome _ => pow_nonneg (valueNonnegative outcome) _)
  have productIdentity (outcome : Outcome) :
      weight outcome * value outcome *
        (value outcome ^ (power - 1)) ^ (((order : ℝ) - 1) / ((power : ℝ) - 1)) =
      weight outcome * value outcome ^ order := by
    have exponentIdentity : ((power - 1 : ℕ) : ℝ) *
        (((order : ℝ) - 1) / ((power : ℝ) - 1)) = ((order - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ power), Nat.cast_sub orderPositive, Nat.cast_one]
      field_simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (valueNonnegative outcome), exponentIdentity,
      Real.rpow_natCast, mul_assoc, ← pow_succ', Nat.sub_add_cancel orderPositive]
  have meanPower (outcome : Outcome) :
      weight outcome * value outcome * value outcome ^ (power - 1) =
        weight outcome * value outcome ^ power := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ power)]
  simpa only [smul_eq_mul, productIdentity, meanPower] using interpolation

/-- A sublinear mixed-moment remainder cannot destroy the strict contraction
of the pure moment coefficient. -/
theorem exists_uniform_bound_of_sublinear_recursion {sequence : ℕ → ℝ}
    {coefficient remainder exponent : ℝ}
    (coefficientNonnegative : 0 ≤ coefficient) (coefficientBelowOne : coefficient < 1)
    (remainderNonnegative : 0 ≤ remainder)
    (exponentNonnegative : 0 ≤ exponent) (exponentBelowOne : exponent < 1)
    (nonnegative : ∀ depth, 0 ≤ sequence depth)
    (step : ∀ depth, sequence (depth + 1) ≤
      coefficient * sequence depth + remainder * sequence depth ^ exponent) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth, sequence depth ≤ bound := by
  have gapPositive : 0 < 1 - coefficient := sub_pos.mpr coefficientBelowOne
  have growth := tendsto_rpow_atTop (sub_pos.mpr exponentBelowOne)
  obtain ⟨bound, boundLarge, remainderBound⟩ :=
    ((eventually_ge_atTop (max 1 (sequence 0))).and
      (growth.eventually (eventually_ge_atTop (remainder / (1 - coefficient))))).exists
  have boundAtLeastOne : 1 ≤ bound := (le_max_left _ _).trans boundLarge
  have boundPositive : 0 < bound := zero_lt_one.trans_le boundAtLeastOne
  have remainderControl : remainder ≤ (1 - coefficient) * bound ^ (1 - exponent) := by
    have control := (div_le_iff₀ gapPositive).mp remainderBound
    simpa only [mul_comm] using control
  have invariant : coefficient * bound + remainder * bound ^ exponent ≤ bound := by
    have control := mul_le_mul_of_nonneg_right remainderControl
      (Real.rpow_nonneg boundPositive.le exponent)
    rw [mul_assoc, ← Real.rpow_add boundPositive, sub_add_cancel, Real.rpow_one] at control
    nlinarith
  refine ⟨bound, boundAtLeastOne, ?_⟩
  intro depth
  induction depth with
  | zero => exact (le_max_right _ _).trans boundLarge
  | succ depth inductionHypothesis =>
      exact (step depth).trans ((add_le_add
        (mul_le_mul_of_nonneg_left inductionHypothesis coefficientNonnegative)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (nonnegative depth) inductionHypothesis exponentNonnegative)
          remainderNonnegative)).trans invariant)

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

theorem finite_product_mixed_moment_le_sublinear {Edge : Type*} [Fintype Edge]
    (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (meanOne : ∀ edge, ∑ outcome, weight edge outcome * value edge outcome = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) {moment : ℝ} (momentAtLeastOne : 1 ≤ moment)
    (highMomentBound : ∀ edge, (∑ outcome, weight edge outcome * value edge outcome ^ power) ≤ moment)
    (orders : Edge → ℕ) (ordersBound : ∀ edge, orders edge ≤ power)
    (predecessorSum : (∑ edge, (orders edge - 1)) ≤ power - 2) :
    (∏ edge, ∑ outcome, weight edge outcome * value edge outcome ^ orders edge) ≤
      moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have denominatorPositive : 0 < (power : ℝ) - 1 := by
    have bound : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have localBound (edge : Edge) :
      (∑ outcome, weight edge outcome * value edge outcome ^ orders edge) ≤
        moment ^ (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
    by_cases zeroOrder : orders edge = 0
    · simp only [zeroOrder, pow_zero, mul_one, normalized, Nat.zero_sub,
        Nat.cast_zero, zero_div, Real.rpow_zero, le_refl]
    · have positiveOrder : 1 ≤ orders edge := Nat.one_le_iff_ne_zero.mpr zeroOrder
      have interpolation := finite_mean_one_moment_interpolation (weight edge) (value edge)
        (weightNonnegative edge) (valueNonnegative edge) (meanOne edge)
        powerAtLeastTwo positiveOrder (ordersBound edge)
      have orderCast : ((orders edge - 1 : ℕ) : ℝ) = (orders edge : ℝ) - 1 := by
        rw [Nat.cast_sub positiveOrder, Nat.cast_one]
      rw [orderCast]
      exact interpolation.trans (Real.rpow_le_rpow
        (Finset.sum_nonneg (fun outcome _ => mul_nonneg
          (weightNonnegative edge outcome) (pow_nonneg (valueNonnegative edge outcome) power)))
        (highMomentBound edge) (div_nonneg
          (sub_nonneg.mpr (by exact_mod_cast positiveOrder)) denominatorPositive.le))
  calc
    _ ≤ ∏ edge, moment ^ (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1)) :=
      Finset.prod_le_prod (fun edge _ => Finset.sum_nonneg (fun outcome _ =>
        mul_nonneg (weightNonnegative edge outcome) (pow_nonneg (valueNonnegative edge outcome) _)))
        (fun edge _ => localBound edge)
    _ = moment ^ (∑ edge, (((orders edge - 1 : ℕ) : ℝ) / ((power : ℝ) - 1))) :=
      (Real.rpow_sum_of_pos (zero_lt_one.trans_le momentAtLeastOne) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le momentAtLeastOne
      rw [← Finset.sum_div, ← Nat.cast_sum]
      exact div_le_div_of_nonneg_right (by exact_mod_cast predecessorSum) denominatorPositive.le

theorem finite_product_nonconstant_assignment_moment_le_sublinear {Edge : Type*}
    [Fintype Edge] [DecidableEq Edge] (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (meanOne : ∀ edge, ∑ outcome, weight edge outcome * value edge outcome = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) {moment : ℝ} (momentAtLeastOne : 1 ≤ moment)
    (highMomentBound : ∀ edge, (∑ outcome, weight edge outcome * value edge outcome ^ power) ≤ moment)
    (assignment : Fin power → Edge) (nonconstant : ¬ ∃ edge, assignment = fun _ => edge) :
    (∏ edge, ∑ outcome, weight edge outcome *
      value edge outcome ^ Fintype.card {factor : Fin power // assignment factor = edge}) ≤
      moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  apply finite_product_mixed_moment_le_sublinear weight value weightNonnegative valueNonnegative
    normalized meanOne powerAtLeastTwo momentAtLeastOne highMomentBound
    (fun edge => Fintype.card {factor : Fin power // assignment factor = edge})
  · intro edge
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun factor : Fin power => assignment factor = edge)
  · exact nonconstant_assignment_sum_predecessor_orders powerAtLeastTwo assignment nonconstant

theorem finite_product_constant_assignment_moment {Edge : Type*}
    [Fintype Edge] [DecidableEq Edge] (weight value : Edge → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1) (power : ℕ) (chosen : Edge) :
    (∏ edge, ∑ outcome, weight edge outcome *
      value edge outcome ^ Fintype.card {factor : Fin power // (fun _ => chosen) factor = edge}) =
      ∑ outcome, weight chosen outcome * value chosen outcome ^ power := by
  classical
  have localIdentity (edge : Edge) :
      (∑ outcome, weight edge outcome *
        value edge outcome ^ Fintype.card {factor : Fin power // (fun _ => chosen) factor = edge}) =
        if chosen = edge then ∑ outcome, weight edge outcome * value edge outcome ^ power else 1 := by
    by_cases equal : chosen = edge
    · subst edge
      simp
    · simp only [equal, if_false, Fintype.card_subtype, Finset.filter_false,
        Finset.card_empty, pow_zero, mul_one, normalized]
  simp_rw [localIdentity]
  exact Fintype.prod_ite_eq chosen _

/-- The pure assignments contribute only one top-order moment per coordinate;
every other assignment has the strictly sublinear moment exponent. -/
theorem finite_product_sum_moment_le_linear_add_sublinear {Edge : Type*}
    [Fintype Edge] [DecidableEq Edge] (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (meanOne : ∀ edge, ∑ outcome, weight edge outcome * value edge outcome = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) {moment : ℝ} (momentAtLeastOne : 1 ≤ moment)
    (highMomentBound : ∀ edge, (∑ outcome, weight edge outcome * value edge outcome ^ power) ≤ moment) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge, value edge (outcome edge)) ^ power) ≤
        Fintype.card Edge * moment + (Fintype.card Edge : ℝ) ^ power *
          moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  classical
  rw [Universality.finite_product_sum_moment]
  have constantInjective : Function.Injective (fun edge : Edge => (fun _ : Fin power => edge)) := by
    intro first second equal
    exact congrFun equal ⟨0, by omega⟩
  have pureSum :
      (∑ assignment : Fin power → Edge,
        if assignment ∈ Finset.univ.image (fun edge : Edge => (fun _ : Fin power => edge))
          then moment else 0) = Fintype.card Edge * moment := by
    rw [← Finset.sum_filter]
    have filterIdentity : (Finset.univ.filter (fun assignment : Fin power → Edge =>
        assignment ∈ Finset.univ.image (fun edge : Edge => (fun _ : Fin power => edge)))) =
        Finset.univ.image (fun edge : Edge => (fun _ : Fin power => edge)) := by
      ext assignment
      simp
    rw [filterIdentity, Finset.sum_const, Finset.card_image_of_injective _ constantInjective]
    simp only [Finset.card_univ, nsmul_eq_mul]
  have assignmentBound (assignment : Fin power → Edge) :
      (∏ edge, ∑ outcome, weight edge outcome *
        value edge outcome ^ Fintype.card {factor : Fin power // assignment factor = edge}) ≤
      (if assignment ∈ Finset.univ.image (fun edge : Edge => (fun _ : Fin power => edge))
          then moment else 0) + moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
    by_cases constant : assignment ∈ Finset.univ.image
        (fun edge : Edge => (fun _ : Fin power => edge))
    · rw [if_pos constant]
      obtain ⟨chosen, _, rfl⟩ := Finset.mem_image.mp constant
      rw [finite_product_constant_assignment_moment weight value normalized]
      exact (highMomentBound chosen).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (zero_lt_one.trans_le momentAtLeastOne).le _))
    · rw [if_neg constant, zero_add]
      apply finite_product_nonconstant_assignment_moment_le_sublinear weight value
        weightNonnegative valueNonnegative normalized meanOne powerAtLeastTwo
        momentAtLeastOne highMomentBound assignment
      rintro ⟨chosen, rfl⟩
      exact constant (Finset.mem_image.mpr ⟨chosen, Finset.mem_univ _, rfl⟩)
  calc
    _ ≤ ∑ assignment : Fin power → Edge,
      ((if assignment ∈ Finset.univ.image (fun edge : Edge => (fun _ : Fin power => edge))
          then moment else 0) + moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) :=
      Finset.sum_le_sum (fun assignment _ => assignmentBound assignment)
    _ = _ := by
      rw [Finset.sum_add_distrib, pureSum, Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

/-- Unused coordinates of a normalized finite product law integrate to one.
This allows a selected path to use only the coordinates it actually contains. -/
theorem finite_product_restrict_observable {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (weight : Edge → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge) (response : (path → Outcome) → ℝ) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      response (fun edge : path => outcome edge)) =
      ∑ outcome : path → Outcome, (∏ edge : path, weight edge (outcome edge)) * response outcome := by
  classical
  rw [← (Equiv.piEquivPiSubtypeProd (fun edge => edge ∈ path) (fun _ => Outcome)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro retained _
  have factor (omitted : {edge : Edge // edge ∉ path} → Outcome) :
      (∏ edge, weight edge
        ((Equiv.piEquivPiSubtypeProd (fun edge => edge ∈ path) (fun _ => Outcome)).symm
          (retained, omitted) edge)) =
        (∏ edge : path, weight edge (retained edge)) *
          ∏ edge : {edge : Edge // edge ∉ path}, weight edge (omitted edge) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun edge => edge ∈ path)]
    congr 1
    · apply Finset.prod_congr (by ext; simp)
      intro edge _
      simp [Equiv.piEquivPiSubtypeProd, edge.property]
    · apply Finset.prod_congr (by ext; simp)
      intro edge _
      simp [Equiv.piEquivPiSubtypeProd, edge.property]
  have restriction (omitted : {edge : Edge // edge ∉ path} → Outcome) :
      (fun edge : path =>
        (Equiv.piEquivPiSubtypeProd (fun edge => edge ∈ path) (fun _ => Outcome)).symm
          (retained, omitted) edge) = retained := by
    funext edge
    simp [Equiv.piEquivPiSubtypeProd, edge.property]
  simp_rw [factor, restriction]
  calc
    _ = ((∏ edge : path, weight edge (retained edge)) * response retained) *
        ∑ omitted : {edge : Edge // edge ∉ path} → Outcome,
          ∏ edge : {edge : Edge // edge ∉ path}, weight edge (omitted edge) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omitted _
      ring
    _ = _ := by
      rw [← Fintype.prod_sum]
      simp only [normalized, Finset.prod_const_one, mul_one]

theorem finite_product_path_sum_moment_bound {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge)
    (meanOne : ∀ edge ∈ path, ∑ outcome, weight edge outcome * value edge outcome = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) {moment : ℝ} (momentAtLeastOne : 1 ≤ moment)
    (highMomentBound : ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * value edge outcome ^ power) ≤ moment) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge ∈ path, value edge (outcome edge)) ^ power) ≤
        path.card * moment + (path.card : ℝ) ^ power *
          moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have restricted := finite_product_restrict_observable weight normalized path
    (fun outcome : path → Outcome => (∑ edge : path, value edge (outcome edge)) ^ power)
  have sumPath (outcome : Edge → Outcome) :
      (∑ edge : path, value edge (outcome edge)) = ∑ edge ∈ path, value edge (outcome edge) := by
    exact Finset.sum_coe_sort path (fun edge => value edge (outcome edge))
  simp_rw [sumPath] at restricted
  rw [restricted]
  simpa only [Fintype.card_coe] using finite_product_sum_moment_le_linear_add_sublinear
    (fun edge : path => weight edge) (fun edge : path => value edge)
    (fun edge => weightNonnegative edge) (fun edge => valueNonnegative edge)
    (fun edge => normalized edge) (fun edge => meanOne edge edge.property)
    powerAtLeastTwo momentAtLeastOne (fun edge => highMomentBound edge edge.property)

/-- Averaging the selected-path bound preserves the expected path length as
the coefficient of the top moment.  In particular, the pure coefficient is
not replaced by the maximal path length to the power `power`. -/
theorem selected_path_moment_bound {Root Edge : Type*} [Fintype Root] [Fintype Edge]
    [DecidableEq Edge] (rootWeight : Root → ℝ) (family : Root → PathFamily Edge)
    (selected : Root → Finset Edge) (selectedMember : ∀ root, selected root ∈ (family root).paths)
    (weight value : Root → Edge → Outcome → ℝ)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (valueNonnegative : ∀ root edge outcome, 0 ≤ value root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    (meanOne : ∀ root edge, edge ∈ selected root →
      ∑ outcome, weight root edge outcome * value root edge outcome = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) {moment : ℝ} (momentAtLeastOne : 1 ≤ moment)
    (highMomentBound : ∀ root edge, edge ∈ selected root →
      (∑ outcome, weight root edge outcome * value root edge outcome ^ power) ≤ moment) :
    (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
      (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge)) ^ power) ≤
      (∑ root, rootWeight root * (selected root).card) * moment +
        (∑ root, rootWeight root * ((selected root).card : ℝ) ^ power) *
          moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have rootBound (root : Root) :
      (∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge)) ^ power) ≤
      (selected root).card * moment + ((selected root).card : ℝ) ^ power *
        moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
    calc
      _ ≤ ∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
          (∑ edge ∈ selected root, value root edge (outcome edge)) ^ power := by
        apply Finset.sum_le_sum
        intro outcome _
        apply mul_le_mul_of_nonneg_left _
          (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
        exact pow_le_pow_left₀
          ((family root).shortest_nonneg (fun edge => valueNonnegative root edge (outcome edge)))
          ((family root).shortest_le_pathCost _ (selectedMember root)) power
      _ ≤ _ := finite_product_path_sum_moment_bound (weight root) (value root)
        (weightNonnegative root) (valueNonnegative root) (normalized root) (selected root)
        (meanOne root) powerAtLeastTwo momentAtLeastOne (highMomentBound root)
  calc
    _ ≤ ∑ root, rootWeight root *
        ((selected root).card * moment + ((selected root).card : ℝ) ^ power *
          moment ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left (rootBound root) (rootNonnegative root))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

theorem finite_product_path_mean {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (weight value : Edge → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge)
    (meanOne : ∀ edge ∈ path, ∑ outcome, weight edge outcome * value edge outcome = 1) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge ∈ path, value edge (outcome edge))) = (path.card : ℝ) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have localMean (edge : Edge) (within : edge ∈ path) :
      (∑ outcome : Edge → Outcome, (∏ other, weight other (outcome other)) *
        value edge (outcome edge)) = 1 := by
    rw [Universality.finite_product_local_moment weight (value edge) edge]
    simp only [normalized, Finset.prod_const_one, one_mul, meanOne edge within]
  calc
    _ = ∑ _edge ∈ path, (1 : ℝ) := Finset.sum_congr rfl localMean
    _ = _ := by simp

/-- The lower mean comes from common (pivotal) edges.  No lower bound by the
unweighted graph distance is asserted for arbitrary weighted inputs. -/
theorem selected_path_mean_bounds {Root Edge : Type*} [Fintype Root] [Fintype Edge]
    [DecidableEq Edge] (rootWeight : Root → ℝ) (family : Root → PathFamily Edge)
    (selected : Root → Finset Edge) (selectedMember : ∀ root, selected root ∈ (family root).paths)
    (weight value : Root → Edge → Outcome → ℝ)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (valueNonnegative : ∀ root edge outcome, 0 ≤ value root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    (meanOne : ∀ root edge, edge ∈ selected root →
      ∑ outcome, weight root edge outcome * value root edge outcome = 1) :
    (∑ root, rootWeight root * ((family root).commonEdges.card : ℝ)) ≤
      (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
        (∏ edge, weight root edge (outcome edge)) *
          (family root).shortest (fun edge => value root edge (outcome edge))) ∧
    (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
      (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge))) ≤
      ∑ root, rootWeight root * ((selected root).card : ℝ) := by
  have lowerMean (root : Root) :
      ((family root).commonEdges.card : ℝ) ≤
      ∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge)) := by
    rw [← finite_product_path_mean (weight root) (value root) (normalized root)
      (family root).commonEdges (fun edge within => meanOne root edge
        ((family root).commonEdges_subset (selectedMember root) within))]
    apply Finset.sum_le_sum
    intro outcome _
    exact mul_le_mul_of_nonneg_left
      ((family root).commonEdges_cost_le_shortest (fun edge => valueNonnegative root edge (outcome edge)))
      (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
  have upperMean (root : Root) :
      (∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge))) ≤
      ((selected root).card : ℝ) := by
    rw [← finite_product_path_mean (weight root) (value root) (normalized root)
      (selected root) (meanOne root)]
    apply Finset.sum_le_sum
    intro outcome _
    exact mul_le_mul_of_nonneg_left ((family root).shortest_le_pathCost _ (selectedMember root))
      (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
  exact ⟨Finset.sum_le_sum (fun root _ =>
    mul_le_mul_of_nonneg_left (lowerMean root) (rootNonnegative root)),
    Finset.sum_le_sum (fun root _ =>
      mul_le_mul_of_nonneg_left (upperMean root) (rootNonnegative root))⟩

end
end IGSIII.Chemical.SmallBall
