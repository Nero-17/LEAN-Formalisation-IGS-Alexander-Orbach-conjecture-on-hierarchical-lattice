import IGSIII.Chemical.SmallBall.FiniteDepthExponential
import IGSIII.Chemical.SmallBall.FiniteDepthSmallBall

set_option autoImplicit false

/-! Manuscript indexing starts with the single-edge seed.  IGS II's
`generation 0` is the first rule graph, so it occurs at manuscript level one. -/

namespace IGSIII.Chemical.SmallBall

open Universality

noncomputable section

def manuscriptDistanceMean (rule : Rule) (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | depth + 1 => conditionedDistanceMean (rule.generation depth).network p

def manuscriptNormalizedMoment (rule : Rule) (p : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | depth + 1, power => normalizedDistanceMoment (rule.generation depth).network p power

def manuscriptExponentialMoment (rule : Rule) (p : ℝ) : ℕ → ℝ → ℝ
  | 0, parameter => Real.exp parameter
  | depth + 1, parameter => normalizedDistanceExponentialMoment (rule.generation depth).network p parameter

def manuscriptInverseMoment (rule : Rule) (p : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | depth + 1, power => ∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
      (normalizedDistance (rule.generation depth).network p configuration)⁻¹ ^ power

def manuscriptRealMoment (rule : Rule) (p : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | depth + 1, exponent => ∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
      normalizedDistance (rule.generation depth).network p configuration ^ exponent

theorem exists_uniform_manuscript_positive_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) (power : ℕ) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth, manuscriptNormalizedMoment rule p depth power ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_positive_moment rule simple p positive lessOne fixedPoint scale power
  refine ⟨max 1 bound, le_max_left _ _, fun depth => ?_⟩
  cases depth with
  | zero => exact le_max_left _ _
  | succ depth => exact (valid depth).trans (le_max_right _ _)

theorem exists_uniform_manuscript_factorial_moments (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ depth power,
      manuscriptNormalizedMoment rule p depth power ≤ constant ^ power * (power.factorial : ℝ) := by
  obtain ⟨constant, constantAtLeastOne, valid⟩ :=
    exists_uniform_generation_factorial_moments rule simple p positive lessOne fixedPoint scale
  refine ⟨constant, constantAtLeastOne, fun depth power => ?_⟩
  cases depth with
  | zero =>
      exact (one_le_pow₀ constantAtLeastOne).trans (le_mul_of_one_le_right
        (pow_nonneg (zero_le_one.trans constantAtLeastOne) power)
        (by exact_mod_cast Nat.factorial_pos power))
  | succ depth => exact valid depth power

theorem exists_uniform_manuscript_exponential_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) :
    ∃ bound : ℝ, ∀ depth, manuscriptExponentialMoment rule p depth parameter ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_exponential_moment
    rule simple p positive lessOne fixedPoint scale parameter parameterNonnegative
  refine ⟨max (Real.exp parameter) bound, fun depth => ?_⟩
  cases depth with
  | zero => exact le_max_left _ _
  | succ depth => exact (valid depth).trans (le_max_right _ _)

theorem exists_uniform_manuscript_inverse_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) (power : ℕ) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth, manuscriptInverseMoment rule p depth power ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_inverse_moment rule simple p positive lessOne fixedPoint scale power
  refine ⟨max 1 bound, le_max_left _ _, fun depth => ?_⟩
  cases depth with
  | zero => exact le_max_left _ _
  | succ depth => exact (valid depth).trans (le_max_right _ _)

theorem exists_uniform_manuscript_real_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) (exponent : ℝ) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth, manuscriptRealMoment rule p depth exponent ≤ bound := by
  have generationBound : ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        normalizedDistance (rule.generation depth).network p configuration ^ exponent) ≤ bound := by
    by_cases exponentNonnegative : 0 ≤ exponent
    · exact exists_uniform_generation_real_positive_moment rule simple p positive lessOne fixedPoint scale exponentNonnegative
    · simpa only [neg_neg] using exists_uniform_generation_real_inverse_moment rule simple p positive lessOne fixedPoint scale
        (exponent := -exponent) (neg_nonneg.mpr (le_of_not_ge exponentNonnegative))
  obtain ⟨bound, valid⟩ := generationBound
  refine ⟨max 1 bound, le_max_left _ _, fun depth => ?_⟩
  cases depth with
  | zero => exact le_max_left _ _
  | succ depth => exact (valid depth).trans (le_max_right _ _)

end
end IGSIII.Chemical.SmallBall
