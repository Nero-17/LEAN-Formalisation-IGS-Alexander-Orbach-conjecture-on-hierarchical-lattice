import Universality.Percolation.FiniteNetwork
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# The finite Bernoulli product law

This file connects edge configurations with their actual probability weights.
The crossing event is graph reachability.  Conditional expectations use the
finite weighted sums, rather than assigning the desired matrix by definition.
-/

namespace Universality
namespace FiniteNetwork

noncomputable section

variable {vertices edges : ℕ}

def bernoulliWeight (p : ℝ) (ω : Configuration edges) : ℝ :=
  ∏ e : Fin edges, if ω e then p else 1 - p

theorem bernoulliWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (ω : Configuration edges) : 0 ≤ bernoulliWeight p ω := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact hp
  · exact sub_nonneg.mpr hp'

theorem sum_bernoulliWeight (p : ℝ) :
    ∑ ω : Configuration edges, bernoulliWeight p ω = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sum (fun (_ : Fin edges) (opened : Bool) =>
    if opened then p else 1 - p)]
  simp

theorem bernoulliWeight_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (ω : Configuration edges) : 0 < bernoulliWeight p ω := by
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · exact sub_pos.mpr hp'

theorem bernoulliWeight_half (ω : Configuration edges) :
    bernoulliWeight (1 / 2) ω = (1 / 2 : ℝ) ^ edges := by
  simp only [bernoulliWeight, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ite_self, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def reliability (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  ∑ ω : Configuration edges, if R.crosses ω then bernoulliWeight p ω else 0

def conditioningProbability (R : FiniteNetwork vertices edges) (p : ℝ)
    (σ : LiveState) : ℝ :=
  ∑ ω : Configuration edges,
    if R.conditioning σ ω then bernoulliWeight p ω else 0

def massMatrix (R : FiniteNetwork vertices edges) (p : ℝ) :
    Matrix LiveState LiveState ℝ :=
  fun σ τ =>
    (∑ ω : Configuration edges,
      if R.conditioning σ ω then bernoulliWeight p ω * R.liveCount σ τ ω else 0) /
    R.conditioningProbability p σ

theorem reliability_nonneg (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ R.reliability p := by
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact bernoulliWeight_nonneg hp hp' ω
  · exact le_rfl

theorem reliability_le_one (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : R.reliability p ≤ 1 := by
  rw [← sum_bernoulliWeight (edges := edges) p]
  apply Finset.sum_le_sum
  intro ω _
  split
  · exact le_rfl
  · exact bernoulliWeight_nonneg hp hp' ω

theorem conditioningProbability_half (R : FiniteNetwork vertices edges) (σ : LiveState) :
    R.conditioningProbability (1 / 2) σ =
      (1 / 2 : ℝ) ^ edges * R.conditioningCount σ := by
  simp only [conditioningProbability, bernoulliWeight_half, conditioningCount]
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem conditional_weighted_sum_half (R : FiniteNetwork vertices edges) (σ τ : LiveState) :
    (∑ ω : Configuration edges,
      if R.conditioning σ ω then bernoulliWeight (1 / 2) ω * R.liveCount σ τ ω else 0) =
      (1 / 2 : ℝ) ^ edges * R.conditionalCount σ τ := by
  simp only [bernoulliWeight_half, conditionalCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split <;> simp_all

/-- The rational counting matrix really equals the Bernoulli conditional
expectation at parameter one half. The equality also respects the totalised
division convention if a conditioning event has probability zero. -/
theorem massMatrix_half (R : FiniteNetwork vertices edges) (σ τ : LiveState) :
    R.massMatrix (1 / 2) σ τ = (R.fairMassMatrix σ τ : ℝ) := by
  simp only [massMatrix, conditional_weighted_sum_half, conditioningProbability_half,
    fairMassMatrix, Rat.cast_div, Rat.cast_natCast]
  exact mul_div_mul_left _ _ (by positivity)

end
end FiniteNetwork
end Universality
