import Universality.Percolation.ClusterNumberRecursion
import Universality.Percolation.CountingPolynomials

namespace Universality.FiniteNetwork
noncomputable section
open Polynomial

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def internalClusterCountByOpenSize (k : ℕ) : ℕ :=
  ∑ configuration : Configuration edges,
    if openCount configuration = k then (R.internalClusterFamily configuration).card else 0

def internalClusterPolynomial : Polynomial ℤ :=
  ∑ configuration : Configuration edges,
    ((R.internalClusterFamily configuration).card : Polynomial ℤ) *
      X ^ openCount configuration * (1 - X) ^ (edges - openCount configuration)

theorem internalClusterPolynomial_bernstein :
    R.internalClusterPolynomial = ∑ k ∈ Finset.range (edges + 1),
      (R.internalClusterCountByOpenSize k : Polynomial ℤ) * X ^ k * (1 - X) ^ (edges - k) := by
  classical
  unfold internalClusterPolynomial internalClusterCountByOpenSize
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  have hrange : openCount configuration ∈ Finset.range (edges + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (openCount_le configuration))
  simp [hrange]

theorem internalClusterPolynomial_eval (p : ℝ) :
    (R.internalClusterPolynomial).eval₂ (Int.castRingHom ℝ) p =
      R.expectedInternalClusterNumber p := by
  unfold internalClusterPolynomial expectedInternalClusterNumber
  simp only [eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro configuration _
  simp only [eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_one, eval₂_natCast,
    bernoulliWeight_eq_bernstein]
  ring

end
end Universality.FiniteNetwork
