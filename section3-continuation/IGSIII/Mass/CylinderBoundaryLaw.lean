import IGSIII.Mass.RetainedCylinderWeights
import Universality.Probability.FiniteWeightMeasure
import Universality.Probability.MarkovTrajectory

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

variable {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]

omit [DecidableEq Alphabet] in
theorem compatible_tree_child_weight_le (weight : List (Alphabet) → ℝ)
    (nonnegative : ∀ address, 0 ≤ weight address)
    (compatible : ∀ address, weight address = ∑ edge, weight (address ++ [edge]))
    (address : List (Alphabet)) (edge : Alphabet) : weight (address ++ [edge]) ≤ weight address := by
  rw [compatible address]
  exact Finset.single_le_sum (f := fun other => weight (address ++ [other]))
    (fun other _ => nonnegative _) (Finset.mem_univ edge)

def cylinderWordTransitionWeight (fallback : Alphabet) (weight : List (Alphabet) → ℝ)
    (depth : ℕ) (before : Fin depth → Alphabet) (after : Fin (depth + 1) → Alphabet) : ℝ :=
  if Fin.init after = before then
    if 0 < weight (List.ofFn before) then weight (List.ofFn after) / weight (List.ofFn before)
    else if after (Fin.last depth) = fallback then 1 else 0
  else 0

omit [Fintype Alphabet] in
theorem cylinderWordTransitionWeight_nonnegative (fallback : Alphabet)
    (weight : List (Alphabet) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (depth : ℕ) (before : Fin depth → Alphabet) (after : Fin (depth + 1) → Alphabet) :
    0 ≤ cylinderWordTransitionWeight fallback weight depth before after := by
  unfold cylinderWordTransitionWeight
  split_ifs with _ positive _
  · exact div_nonneg (nonnegative _) positive.le
  · exact zero_le_one
  · exact le_rfl
  · exact le_rfl

theorem cylinderWordTransitionWeight_sum (fallback : Alphabet)
    (weight : List (Alphabet) → ℝ)
    (compatible : ∀ address, weight address = ∑ edge, weight (address ++ [edge]))
    (depth : ℕ) (before : Fin depth → Alphabet) :
    ∑ after : Fin (depth + 1) → Alphabet, cylinderWordTransitionWeight fallback weight depth before after = 1 := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (depth + 1) => Alphabet)).sum_comp
    (cylinderWordTransitionWeight fallback weight depth before)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, cylinderWordTransitionWeight, Fin.init_snoc, Fin.snoc_last,
    List.ofFn_succ', Fin.snoc_castSucc, List.concat_eq_append]
  by_cases positive : 0 < weight (List.ofFn before)
  · simp only [positive, if_true]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← Finset.sum_div, ← compatible, div_self positive.ne']
  · simp only [positive, if_false]
    simp

theorem cylinderWordTransitionWeight_step (fallback : Alphabet)
    (weight : List (Alphabet) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (compatible : ∀ address, weight address = ∑ edge, weight (address ++ [edge]))
    (depth : ℕ) (after : Fin (depth + 1) → Alphabet) :
    ∑ before : Fin depth → Alphabet, weight (List.ofFn before) *
      cylinderWordTransitionWeight fallback weight depth before after = weight (List.ofFn after) := by
  classical
  rw [Finset.sum_eq_single (Fin.init after)]
  · unfold cylinderWordTransitionWeight
    rw [if_pos rfl]
    by_cases positive : 0 < weight (List.ofFn (Fin.init after))
    · rw [if_pos positive]
      field_simp
    · have parent_zero : weight (List.ofFn (Fin.init after)) = 0 := le_antisymm (le_of_not_gt positive) (nonnegative _)
      have child_bound := compatible_tree_child_weight_le weight nonnegative compatible (List.ofFn (Fin.init after)) (after (Fin.last depth))
      have word_identity : List.ofFn after = List.ofFn (Fin.init after) ++ [after (Fin.last depth)] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        rfl
      rw [← word_identity, parent_zero] at child_bound
      have child_zero : weight (List.ofFn after) = 0 := le_antisymm child_bound (nonnegative _)
      simp only [parent_zero, zero_mul, child_zero]
  · intro before _ different
    have mismatch : Fin.init after ≠ before := Ne.symm different
    simp only [cylinderWordTransitionWeight, if_neg mismatch, mul_zero]
  · simp

variable [MeasurableSpace Alphabet] [MeasurableSingletonClass Alphabet]
variable (fallback : Alphabet) (weight : List (Alphabet) → ℝ)
variable (nonnegative : ∀ address, 0 ≤ weight address) (root_one : weight [] = 1)
variable (compatible : ∀ address, weight address = ∑ edge, weight (address ++ [edge]))

def cylinderWordLaw (depth : ℕ) : Measure (Fin depth → Alphabet) :=
  (finiteWeightPMF (fun word => weight (List.ofFn word)) (fun _ => nonnegative _)
    (compatible_tree_weights_sum_one weight root_one compatible depth)).toMeasure

instance cylinderWordLaw_probability (depth : ℕ) : IsProbabilityMeasure (cylinderWordLaw weight nonnegative root_one compatible depth) := by
  unfold cylinderWordLaw
  infer_instance

def cylinderWordTransition (depth : ℕ) : Kernel (Fin depth → Alphabet) (Fin (depth + 1) → Alphabet) :=
  finiteWeightKernel (cylinderWordTransitionWeight fallback weight depth)
    (cylinderWordTransitionWeight_nonnegative fallback weight nonnegative depth)
    (cylinderWordTransitionWeight_sum fallback weight compatible depth)

instance cylinderWordTransition_markov (depth : ℕ) : IsMarkovKernel (cylinderWordTransition fallback weight nonnegative compatible depth) := by
  unfold cylinderWordTransition
  infer_instance

theorem cylinderWordTransition_law (depth : ℕ) :
    cylinderWordTransition fallback weight nonnegative compatible depth ∘ₘ
      cylinderWordLaw weight nonnegative root_one compatible depth =
        cylinderWordLaw weight nonnegative root_one compatible (depth + 1) := by
  apply finiteWeightKernel_comp
  exact cylinderWordTransitionWeight_step fallback weight nonnegative compatible depth

/-- The genuine probability law of nested finite addresses, constructed from
the compatible weights using a Markov trajectory. Zero-mass prefixes receive
a harmless deterministic transition, and retain zero total mass. -/
def cylinderBoundaryLaw : Measure (Π depth, Fin depth → Alphabet) :=
  markovTrajectory (cylinderWordLaw weight nonnegative root_one compatible 0)
    (cylinderWordTransition fallback weight nonnegative compatible)

instance cylinderBoundaryLaw_probability :
    IsProbabilityMeasure (cylinderBoundaryLaw fallback weight nonnegative root_one compatible) := by
  unfold cylinderBoundaryLaw
  infer_instance

theorem cylinderBoundaryLaw_marginal (depth : ℕ) :
    (cylinderBoundaryLaw fallback weight nonnegative root_one compatible).map (fun path => path depth) =
      cylinderWordLaw weight nonnegative root_one compatible depth :=
  markovTrajectory_marginal (cylinderWordLaw weight nonnegative root_one compatible)
    (cylinderWordTransition fallback weight nonnegative compatible)
    (cylinderWordTransition_law fallback weight nonnegative root_one compatible) depth

theorem cylinderBoundaryLaw_atom (depth : ℕ) (word : Fin depth → Alphabet) :
    cylinderBoundaryLaw fallback weight nonnegative root_one compatible {path | path depth = word} =
      ENNReal.ofReal (weight (List.ofFn word)) := by
  have marginal := congrArg (fun measure : Measure (Fin depth → Alphabet) => measure {word})
    (cylinderBoundaryLaw_marginal fallback weight nonnegative root_one compatible depth)
  rw [Measure.map_apply (measurable_pi_apply depth) (measurableSet_singleton word)] at marginal
  exact marginal.trans (finiteWeightPMF_singleton _ _ _ word)

theorem cylinderBoundaryLaw_extends :
    ∀ᵐ path ∂cylinderBoundaryLaw fallback weight nonnegative root_one compatible,
      ∀ depth, Fin.init (path (depth + 1)) = path depth := by
  apply ae_all_iff.mpr
  intro depth
  apply markovTrajectory_step_ae (cylinderWordLaw weight nonnegative root_one compatible 0)
    (cylinderWordTransition fallback weight nonnegative compatible) depth
      (fun before after => Fin.init after = before)
  · exact Set.to_countable _ |>.measurableSet
  · intro before
    apply ae_iff_of_countable.mpr
    intro after positive_mass
    by_contra mismatch
    apply positive_mass
    change finiteWeightKernel _ _ _ before {after} = 0
    rw [finiteWeightKernel_singleton]
    simp only [cylinderWordTransitionWeight, if_neg mismatch, ENNReal.ofReal_zero]

theorem cylinderBoundaryLaw_positive_prefixes :
    ∀ᵐ path ∂cylinderBoundaryLaw fallback weight nonnegative root_one compatible,
      ∀ depth, 0 < weight (List.ofFn (path depth)) := by
  apply ae_all_iff.mpr
  intro depth
  have positive_words : ∀ᵐ word ∂cylinderWordLaw weight nonnegative root_one compatible depth,
      0 < weight (List.ofFn word) := by
    apply ae_iff_of_countable.mpr
    intro word nonzero
    by_contra not_positive
    have zero_weight : weight (List.ofFn word) = 0 :=
      le_antisymm (le_of_not_gt not_positive) (nonnegative _)
    apply nonzero
    change (finiteWeightPMF _ _ _).toMeasure {word} = 0
    rw [finiteWeightPMF_singleton, zero_weight, ENNReal.ofReal_zero]
  rw [← cylinderBoundaryLaw_marginal fallback weight nonnegative root_one compatible depth] at positive_words
  exact ae_of_ae_map (measurable_pi_apply depth).aemeasurable positive_words

end
end IGSIII.Chemical.Substitution
