import IGSIII.Chemical.SubstitutionPaths.ConditionalLaw
import Universality.Probability.FiniteProductMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Full conditional product law of the actual child histories

The extracted children are histories on the established IGS II space. Their
joint law conditional on the root is the product of the already constructed
history laws. The proof transports finite configurations to their unique
coherent histories and gives zero weight to incoherent histories.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem finite_product_pushforward_observable
    {index source target : Type*} [Fintype index] [Fintype source] [Fintype target]
    [DecidableEq index] [DecidableEq target]
    (weight : index → source → ℝ) (transport : source → target)
    (pushedWeight : index → target → ℝ)
    (pushforward : ∀ edge output,
      pushedWeight edge output = ∑ sample, if transport sample = output then weight edge sample else 0)
    (response : (index → target) → ℝ) :
    (∑ output : index → target, (∏ edge, pushedWeight edge (output edge)) * response output) =
      ∑ sample : index → source, (∏ edge, weight edge (sample edge)) *
        response (fun edge => transport (sample edge)) := by
  classical
  simp_rw [pushforward, Fintype.prod_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  rw [Finset.sum_eq_single (fun edge => transport (sample edge))]
  · simp
  · intro output _ different
    have mismatch : ∃ edge, transport (sample edge) ≠ output edge := by
      by_contra allMatch
      push Not at allMatch
      exact different (funext (fun edge => (allMatch edge).symm))
    obtain ⟨edge, mismatch⟩ := mismatch
    have zero : (∏ coordinate, if transport (sample coordinate) = output coordinate then
        weight coordinate (sample coordinate) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ edge) (if_neg mismatch)
    rw [zero, zero_mul]
  · simp

theorem conditional_child_histories_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (coarse : Configuration rule.edges)
    (response : (Fin rule.edges → rule.ConfigurationHistory depth) → ℝ) :
    (∑ children : Fin rule.edges → rule.ConfigurationHistory depth,
      (∏ edge, Rule.ConfigurationHistory.recursiveWeight rule p (coarse edge) depth (children edge)) *
        response children) =
      ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
        (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
          response (fun edge => Rule.ConfigurationHistory.ofFine rule depth (cells edge)) := by
  apply finite_product_pushforward_observable
  intro edge history
  rw [Rule.ConfigurationHistory.recursiveWeight_eq_directWeight rule p positive lessOne fixedPoint]
  exact (Rule.ConfigurationHistory.sum_fine_atom rule p (coarse edge) depth history).symm

/-- Exact joint disintegration for actual extracted child histories. The
product contains the full recursive history laws, including all descendants,
under the crossing state prescribed by each root edge. -/
theorem history_root_child_histories_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : Configuration rule.edges →
      (Fin rule.edges → rule.ConfigurationHistory depth) → ℝ) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p opened (depth + 1) history *
        response (historyRootConfiguration rule depth history) (historyChildHistory rule depth history)) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p opened coarse *
        ∑ children : Fin rule.edges → rule.ConfigurationHistory depth,
          (∏ edge, Rule.ConfigurationHistory.recursiveWeight rule p (coarse edge) depth (children edge)) *
            response coarse children := by
  rw [history_root_children_observable rule p positive lessOne fixedPoint]
  apply Finset.sum_congr rfl
  intro coarse _
  congr 1
  exact (conditional_child_histories_observable rule p positive lessOne fixedPoint depth coarse _).symm

/-- Mixed child moments factor under the actual root-conditioned history
law. The response may use the complete root configuration to select edges. -/
theorem history_child_mixed_moment (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : Configuration rule.edges → Fin rule.edges → rule.ConfigurationHistory depth → ℝ)
    (powers : Fin rule.edges → ℕ) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p opened (depth + 1) history *
        ∏ edge, response (historyRootConfiguration rule depth history) edge
          (historyChildHistory rule depth history edge) ^ powers edge) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p opened coarse *
        ∏ edge, ∑ child : rule.ConfigurationHistory depth,
          Rule.ConfigurationHistory.recursiveWeight rule p (coarse edge) depth child *
            response coarse edge child ^ powers edge := by
  rw [history_root_child_histories_observable rule p positive lessOne fixedPoint opened depth
    (fun coarse children => ∏ edge, response coarse edge (children edge) ^ powers edge)]
  simp_rw [finite_product_mixed_moment]

/-- Exact multinomial expansion on the actual configuration-history space.
Each factor on the right is a genuine conditioned child-history moment. -/
theorem history_child_sum_moment (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : Configuration rule.edges → Fin rule.edges → rule.ConfigurationHistory depth → ℝ)
    (power : ℕ) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p opened (depth + 1) history *
        (∑ edge, response (historyRootConfiguration rule depth history) edge
          (historyChildHistory rule depth history edge)) ^ power) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p opened coarse *
        ∑ assignment : Fin power → Fin rule.edges, ∏ edge,
          ∑ child : rule.ConfigurationHistory depth,
            Rule.ConfigurationHistory.recursiveWeight rule p (coarse edge) depth child *
              response coarse edge child ^ Fintype.card {factor : Fin power // assignment factor = edge} := by
  rw [history_root_child_histories_observable rule p positive lessOne fixedPoint opened depth
    (fun coarse children => (∑ edge, response coarse edge (children edge)) ^ power)]
  simp_rw [finite_product_sum_moment]

end IGSIII.Chemical.Substitution
