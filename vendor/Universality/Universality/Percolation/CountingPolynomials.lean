import Universality.Percolation.ReliabilityPolynomial
import Universality.Percolation.LocalMassResponse

namespace Universality.FiniteNetwork
noncomputable section
open Polynomial
open scoped BigOperators

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- Exact nonnegative integer counts grouped by the number of open edges. -/
def liveCountBySize (σ τ : LiveState) (k : ℕ) : ℕ :=
  ∑ ω : Configuration edges,
    if R.conditioning σ ω && decide (openCount ω = k) then R.liveCount σ τ ω else 0

/-- The paper's counting polynomial, with integer coefficients. -/
def countingPolynomial (σ τ : LiveState) : Polynomial ℤ :=
  ∑ ω : Configuration edges, if R.conditioning σ ω then
    (R.liveCount σ τ ω : Polynomial ℤ) * X ^ openCount ω *
      (1 - X) ^ (edges - openCount ω) else 0

theorem countingPolynomial_bernstein (σ τ : LiveState) :
    R.countingPolynomial σ τ = ∑ k ∈ Finset.range (edges + 1),
      (R.liveCountBySize σ τ k : Polynomial ℤ) * X ^ k * (1 - X) ^ (edges - k) := by
  classical
  unfold countingPolynomial liveCountBySize
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  have hrange : openCount ω ∈ Finset.range (edges + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (openCount_le ω))
  cases hcondition : R.conditioning σ ω
  · simp
  · simp [hrange]

theorem bernoulliWeight_eq_bernstein (p : ℝ) (ω : Configuration edges) :
    bernoulliWeight p ω = p ^ openCount ω * (1 - p) ^ (edges - openCount ω) := by
  have h := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) p) (configurationPolynomial_eq ω)
  simpa only [eval₂_finsetProd, eval₂_pow, eval₂_mul, eval₂_sub, eval₂_one,
    eval₂_X, apply_ite, bernoulliWeight] using h

theorem countingPolynomial_eval (σ τ : LiveState) (p : ℝ) :
    (R.countingPolynomial σ τ).eval₂ (Int.castRingHom ℝ) p =
      ∑ ω : Configuration edges, if R.conditioning σ ω then
        bernoulliWeight p ω * R.liveCount σ τ ω else 0 := by
  simp only [countingPolynomial, eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro ω _
  split
  · simp only [eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_one, eval₂_natCast,
      bernoulliWeight_eq_bernstein]
    ring
  · simp

theorem massMatrix_eq_countingPolynomial (σ τ : LiveState) (p : ℝ) :
    R.massMatrix p σ τ =
      (R.countingPolynomial σ τ).eval₂ (Int.castRingHom ℝ) p /
        (if σ = .connected then R.reliability p else 1 - R.reliability p) := by
  rw [countingPolynomial_eval]
  unfold massMatrix
  cases σ <;> simp [conditioningProbability_connected, conditioningProbability_both,
    conditioningProbability_single]

end
end Universality.FiniteNetwork
