import Universality.Percolation.Bernoulli
import Universality.Percolation.BernoulliVariance
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The independent finite Bernoulli circuit used by Appendix C.
All probabilities here are finite product sums. The graph-reachability
identification is a separate theorem about the actual finite rule. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem finite_product_event_all
    {Index Input : Type*} [Fintype Index] [DecidableEq Index] [Fintype Input]
    (weight : Index → Input → ℝ) (event : Index → Input → Prop) :
    (∑ configuration : Index → Input,
      if ∀ index, event index (configuration index) then
        (∏ index, weight index (configuration index)) else 0) =
      ∏ index, ∑ input, if event index input then weight index input else 0 := by
  calc
    _ = ∑ configuration : Index → Input,
        ∏ index, if event index (configuration index) then weight index (configuration index) else 0 := by
      apply Finset.sum_congr rfl
      intro configuration _
      exact (Fintype.prod_ite_zero (p := fun index => event index (configuration index))
        (f := fun index => weight index (configuration index))).symm
    _ = _ := (Fintype.prod_sum
      (fun index (input : Input) => if event index input then weight index input else 0)).symm

theorem finite_event_complement
    {Input : Type*} [Fintype Input]
    (weight : Input → ℝ) (normalization : ∑ input, weight input = 1)
    (event : Input → Prop) :
    (∑ input, if ¬ event input then weight input else 0) =
      1 - ∑ input, if event input then weight input else 0 := by
  have partition : (∑ input, if ¬ event input then weight input else 0) +
      (∑ input, if event input then weight input else 0) = ∑ input, weight input := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro input _
    by_cases event input <;> simp [*]
  rw [normalization] at partition
  linarith

def pathCrossing (length : ℕ) (configuration : Configuration length) : Prop :=
  ∀ edge, configuration edge = true

def blockWeight (paths length : ℕ) (probability : ℝ)
    (configuration : Fin paths → Configuration length) : ℝ :=
  ∏ path, bernoulliWeight probability (configuration path)

def blockCrossing (paths length : ℕ)
    (configuration : Fin paths → Configuration length) : Prop :=
  ∃ path, pathCrossing length (configuration path)

def chainWeight (blocks paths length : ℕ) (probability : ℝ)
    (configuration : Fin blocks → Fin paths → Configuration length) : ℝ :=
  ∏ block, blockWeight paths length probability (configuration block)

def chainCrossing (blocks paths length : ℕ)
    (configuration : Fin blocks → Fin paths → Configuration length) : Prop :=
  ∀ block, blockCrossing paths length (configuration block)

theorem path_crossing_probability (length : ℕ) (probability : ℝ) :
    (∑ configuration : Configuration length,
      if pathCrossing length configuration then bernoulliWeight probability configuration else 0) =
      probability ^ length := by
  unfold pathCrossing bernoulliWeight
  calc
    _ = ∑ configuration : Configuration length, ∏ edge : Fin length,
        if configuration edge = true then
          (if configuration edge then probability else 1 - probability) else 0 := by
      apply Finset.sum_congr rfl
      intro configuration _
      have identity := (Fintype.prod_ite_zero (p := fun edge => configuration edge = true)
        (f := fun edge => if configuration edge then probability else 1 - probability)).symm
      by_cases allOpened : ∀ edge, configuration edge = true <;> simpa [allOpened] using identity
    _ = _ := by
      have identity := (Fintype.prod_sum
        (fun (_ : Fin length) (opened : Bool) => if opened = true then
          (if opened then probability else 1 - probability) else 0)).symm
      convert identity using 1
      simp

theorem block_weight_normalization (paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      blockWeight paths length probability configuration) = 1 := by
  unfold blockWeight
  rw [← Fintype.prod_sum]
  simp [sum_bernoulliWeight]

theorem block_failure_probability (paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      if ¬ blockCrossing paths length configuration then blockWeight paths length probability configuration else 0) =
      (1 - probability ^ length) ^ paths := by
  have eventRewrite (configuration : Fin paths → Configuration length) :
      (¬ blockCrossing paths length configuration) ↔ ∀ path, ¬ pathCrossing length (configuration path) := by
    simp only [blockCrossing, not_exists]
  simp_rw [eventRewrite, blockWeight]
  have summand (configuration : Fin paths → Configuration length) :
      (if ∀ path, ¬ pathCrossing length (configuration path) then
        ∏ path, bernoulliWeight probability (configuration path) else 0) =
      ∏ path, if ¬ pathCrossing length (configuration path) then
        bernoulliWeight probability (configuration path) else 0 :=
    (Fintype.prod_ite_zero (p := fun path => ¬ pathCrossing length (configuration path))
      (f := fun path => bernoulliWeight probability (configuration path))).symm
      |> fun identity => by
        by_cases allFailed : ∀ path, ¬ pathCrossing length (configuration path)
        <;> simpa [allFailed] using identity
  try simp_rw [summand]
  have identity := (Fintype.prod_sum (fun (_ : Fin paths) configuration =>
    if ¬ pathCrossing length configuration then bernoulliWeight probability configuration else 0)).symm
  calc
    _ = ∏ _ : Fin paths, ∑ configuration : Configuration length,
        if ¬ pathCrossing length configuration then bernoulliWeight probability configuration else 0 := by
      convert identity using 1
    _ = _ := by
      simp_rw [finite_event_complement (bernoulliWeight probability) (sum_bernoulliWeight probability),
        path_crossing_probability]
      simp

theorem block_crossing_probability (paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      if blockCrossing paths length configuration then blockWeight paths length probability configuration else 0) =
      1 - (1 - probability ^ length) ^ paths := by
  have complement := finite_event_complement (blockWeight paths length probability)
    (block_weight_normalization paths length probability) (blockCrossing paths length)
  rw [block_failure_probability] at complement
  linarith

theorem chain_weight_normalization (blocks paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin blocks → Fin paths → Configuration length,
      chainWeight blocks paths length probability configuration) = 1 := by
  unfold chainWeight
  rw [← Fintype.prod_sum]
  simp [block_weight_normalization]

theorem chain_crossing_probability (blocks paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin blocks → Fin paths → Configuration length,
      if chainCrossing blocks paths length configuration then
        chainWeight blocks paths length probability configuration else 0) =
      (1 - (1 - probability ^ length) ^ paths) ^ blocks := by
  unfold chainCrossing chainWeight
  have summand (configuration : Fin blocks → Fin paths → Configuration length) :
      (if ∀ block, blockCrossing paths length (configuration block) then
        ∏ block, blockWeight paths length probability (configuration block) else 0) =
      ∏ block, if blockCrossing paths length (configuration block) then
        blockWeight paths length probability (configuration block) else 0 :=
    (Fintype.prod_ite_zero (p := fun block => blockCrossing paths length (configuration block))
      (f := fun block => blockWeight paths length probability (configuration block))).symm
      |> fun identity => by
        by_cases allCross : ∀ block, blockCrossing paths length (configuration block)
        <;> simpa [allCross] using identity
  try simp_rw [summand]
  have identity := (Fintype.prod_sum (fun (_ : Fin blocks) configuration =>
    if blockCrossing paths length configuration then blockWeight paths length probability configuration else 0)).symm
  calc
    _ = ∑ configuration : Fin blocks → Fin paths → Configuration length,
        ∏ block, if blockCrossing paths length (configuration block) then
          blockWeight paths length probability (configuration block) else 0 := by
      apply Finset.sum_congr rfl
      intro configuration _
      convert summand configuration using 1
      by_cases allCross : ∀ block, blockCrossing paths length (configuration block) <;> simp [allCross]
    _ = ∏ _ : Fin blocks, ∑ configuration : Fin paths → Configuration length,
        if blockCrossing paths length configuration then blockWeight paths length probability configuration else 0 := by
      convert identity using 1
    _ = _ := by simp [block_crossing_probability]

def outerCrossing (chainEvent : Prop) (configuration : Configuration 4) : Prop :=
  (configuration 0 = true ∧ configuration 1 = true) ∨
    (configuration 2 = true ∧ configuration 3 = true ∧ chainEvent)

theorem outer_crossing_probability (probability : ℝ) (chainEvent : Prop) :
    expectation probability (fun configuration : Configuration 4 =>
      if outerCrossing chainEvent configuration then 1 else 0) =
      probability ^ 2 + (1 - probability ^ 2) * probability ^ 2 *
        (if chainEvent then 1 else 0) := by
  have consFourOne (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (1 : Fin 4) = tail 0 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (0 : Fin 3)) = tail 0
    rfl
  have consFourTwo (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (2 : Fin 4) = tail 1 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (1 : Fin 3)) = tail 1
    rfl
  have consFourThree (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (3 : Fin 4) = tail 2 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (2 : Fin 3)) = tail 2
    rfl
  have consThreeOne (head : Bool) (tail : Configuration 2) : (Fin.cons head tail : Configuration 3) (1 : Fin 3) = tail 0 := by
    change (Fin.cons head tail : Configuration 3) (Fin.succ (0 : Fin 2)) = tail 0
    rfl
  have consThreeTwo (head : Bool) (tail : Configuration 2) : (Fin.cons head tail : Configuration 3) (2 : Fin 3) = tail 1 := by
    change (Fin.cons head tail : Configuration 3) (Fin.succ (1 : Fin 2)) = tail 1
    rfl
  have consTwoOne (head : Bool) (tail : Configuration 1) : (Fin.cons head tail : Configuration 2) (1 : Fin 2) = tail 0 := by
    change (Fin.cons head tail : Configuration 2) (Fin.succ (0 : Fin 1)) = tail 0
    rfl
  by_cases chainEvent <;>
    simp [outerCrossing, expectation_cons, expectation_const, Fin.cons_zero,
      consFourOne, consFourTwo, consFourThree, consThreeOne, consThreeTwo, consTwoOne, *] <;> ring

theorem full_circuit_crossing_probability (blocks paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin blocks → Fin paths → Configuration length,
      chainWeight blocks paths length probability configuration *
        expectation probability (fun outer : Configuration 4 =>
          if outerCrossing (chainCrossing blocks paths length configuration) outer then 1 else 0)) =
      probability ^ 2 + (1 - probability ^ 2) * probability ^ 2 *
        (1 - (1 - probability ^ length) ^ paths) ^ blocks := by
  simp_rw [outer_crossing_probability, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, chain_weight_normalization, one_mul]
  congr 1
  have summand (configuration : Fin blocks → Fin paths → Configuration length) :
      chainWeight blocks paths length probability configuration *
          ((1 - probability ^ 2) * probability ^ 2 *
            (if chainCrossing blocks paths length configuration then 1 else 0)) =
        ((1 - probability ^ 2) * probability ^ 2) *
          (if chainCrossing blocks paths length configuration then
            chainWeight blocks paths length probability configuration else 0) := by
    split_ifs <;> ring
  try simp_rw [summand]
  rw [← Finset.mul_sum, chain_crossing_probability]

theorem critical_chain_probability
    (probability chainProbability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (critical : probability ^ 2 + (1 - probability ^ 2) * probability ^ 2 * chainProbability = probability) :
    chainProbability = 1 / (probability * (1 + probability)) := by
  have firstNonzero : probability ≠ 0 := ne_of_gt positive
  have secondNonzero : 1 - probability ≠ 0 := ne_of_gt (by linarith)
  have thirdNonzero : 1 + probability ≠ 0 := ne_of_gt (by linarith)
  apply (eq_div_iff (mul_ne_zero firstNonzero thirdNonzero)).mpr
  have factored : probability * (1 - probability) *
      (chainProbability * (probability * (1 + probability)) - 1) = 0 := by nlinarith [critical]
  have productZero := (mul_eq_zero.mp factored).resolve_left (mul_ne_zero firstNonzero secondNonzero)
  linarith

end
end IGSIII4.SpectralDensity
