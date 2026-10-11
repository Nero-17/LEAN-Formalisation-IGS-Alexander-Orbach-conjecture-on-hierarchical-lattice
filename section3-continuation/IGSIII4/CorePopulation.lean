import IGSIII4.CoreGeneration
import IGSIII.Probability.IndependentTreeShift
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability

def coreEdgeIndicator {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (edge : Fin edges) : ℝ :=
  if edge ∈ terminalCoreEdges network configuration then 1 else 0

theorem coreEdgeIndicator_nonnegative {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (edge : Fin edges) : 0 ≤ coreEdgeIndicator network configuration edge := by
  unfold coreEdgeIndicator
  split_ifs <;> norm_num

theorem coreEdgeIndicator_le_one {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (edge : Fin edges) : coreEdgeIndicator network configuration edge ≤ 1 := by
  unfold coreEdgeIndicator
  split_ifs <;> norm_num

def corePopulation (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    ℕ → List (Fin rule.edges) → ℝ
  | 0, _ => 1
  | depth + 1, address => ∑ edge, coreEdgeIndicator rule.network (marks (address, true)) edge *
      corePopulation rule marks depth (address ++ [edge])

theorem corePopulation_shift (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (addressPrefix address : List (Fin rule.edges)) (depth : ℕ) :
    corePopulation rule (innovationTreeShift rule addressPrefix marks) depth address =
      corePopulation rule marks depth (addressPrefix ++ address) := by
  induction depth generalizing address with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [corePopulation, innovationTreeShift, inductionHypothesis, List.append_assoc]

theorem corePopulation_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ)
    (address : List (Fin rule.edges)) : 0 ≤ corePopulation rule marks depth address := by
  induction depth generalizing address with
  | zero => exact zero_le_one
  | succ depth inductionHypothesis =>
      exact Finset.sum_nonneg (fun edge _ => mul_nonneg (coreEdgeIndicator_nonnegative _ _ _)
        (inductionHypothesis _))

theorem corePopulation_le_pow (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ)
    (address : List (Fin rule.edges)) : corePopulation rule marks depth address ≤ (rule.edges : ℝ) ^ depth := by
  induction depth generalizing address with
  | zero => simp [corePopulation]
  | succ depth inductionHypothesis =>
      calc
        _ ≤ ∑ _edge : Fin rule.edges, (rule.edges : ℝ) ^ depth := by
          apply Finset.sum_le_sum
          intro edge _
          calc
            _ ≤ 1 * corePopulation rule marks depth (address ++ [edge]) :=
              mul_le_mul_of_nonneg_right (coreEdgeIndicator_le_one rule.network (marks (address, true)) edge)
                (corePopulation_nonnegative rule marks depth (address ++ [edge]))
            _ = corePopulation rule marks depth (address ++ [edge]) := one_mul _
            _ ≤ _ := inductionHypothesis _
        _ = _ := by simp [pow_succ, mul_comm]

theorem corePopulation_measurable (rule : Rule) (depth : ℕ) (address : List (Fin rule.edges)) :
    Measurable (fun marks => corePopulation rule marks depth address) := by
  induction depth generalizing address with
  | zero => exact measurable_const
  | succ depth inductionHypothesis =>
      apply Finset.measurable_sum
      intro edge _
      exact ((measurable_of_finite (fun configuration => coreEdgeIndicator rule.network configuration edge)).comp
        (measurable_pi_apply (address, true))).mul (inductionHypothesis _)

theorem corePopulation_integrable (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (depth : ℕ)
    (address : List (Fin rule.edges)) :
    Integrable (fun marks => corePopulation rule marks depth address)
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
  apply (integrable_const ((rule.edges : ℝ) ^ depth)).mono' (corePopulation_measurable rule depth address).aestronglyMeasurable
  filter_upwards [] with marks
  rw [Real.norm_eq_abs, abs_of_nonneg (corePopulation_nonnegative rule marks depth address)]
  exact corePopulation_le_pow rule marks depth address

theorem corePopulation_eq_generation_count (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    corePopulation rule marks (depth + 1) address =
      ((terminalCoreEdges (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth address true)).card : ℝ) := by
  classical
  induction depth generalizing address with
  | zero =>
      simpa only [corePopulation, coreEdgeIndicator, mul_one, Rule.generation, markedGenerationConfiguration] using
        (terminalCoreEdges_card_eq_sum rule.network (marks (address, true))).symm
  | succ depth inductionHypothesis =>
      rw [corePopulation, generation_terminalCore_card_recursion rule classicalRule depth _
        (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) address true),
        markedGenerationConfiguration_root rule marks crossing, markedGenerationConfiguration_topCells]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases retained : edge ∈ terminalCoreEdges rule.network (marks (address, true))
      · have opened : marks (address, true) edge = true :=
          (terminalCoreEdges_open_active rule.network classicalRule.simple _ retained).1
        simp only [coreEdgeIndicator, retained, ite_true, one_mul, opened]
        exact inductionHypothesis _
      · simp only [coreEdgeIndicator, retained, ite_false, zero_mul]

end
end IGSIII4
