import Universality.Percolation.ReliabilityPolynomial
import Universality.Percolation.Wheatstone
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Universality
open FiniteNetwork Polynomial

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem wheatstone_crossing_counts_by_size :
    wheatstoneNetwork.crossingCountBySize 0 = 0 ∧
    wheatstoneNetwork.crossingCountBySize 1 = 0 ∧
    wheatstoneNetwork.crossingCountBySize 2 = 2 ∧
    wheatstoneNetwork.crossingCountBySize 3 = 8 ∧
    wheatstoneNetwork.crossingCountBySize 4 = 5 ∧
    wheatstoneNetwork.crossingCountBySize 5 = 1 := by
  decide

theorem wheatstone_reliabilityPolynomial :
    wheatstoneNetwork.reliabilityPolynomial =
      2 * X ^ 2 + 2 * X ^ 3 - 5 * X ^ 4 + 2 * X ^ 5 := by
  rw [reliabilityPolynomial_bernstein]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := wheatstone_crossing_counts_by_size
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5]
  ring

theorem wheatstone_reliability (p : ℝ) :
    wheatstoneNetwork.reliability p = 2 * p ^ 2 + 2 * p ^ 3 - 5 * p ^ 4 + 2 * p ^ 5 := by
  rw [← wheatstoneNetwork.reliabilityPolynomial_eval p, wheatstone_reliabilityPolynomial]
  simp

theorem wheatstone_fixed_point_factorization (p : ℝ) :
    wheatstoneNetwork.reliability p - p =
      p * (1 - p) * (2 * p - 1) * (1 + p - p ^ 2) := by
  rw [wheatstone_reliability]
  ring

theorem wheatstone_unique_interior_fixed_point {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    wheatstoneNetwork.reliability p = p ↔ p = 1 / 2 := by
  have hlast : 0 < 1 + p - p ^ 2 := by nlinarith
  constructor
  · intro h
    have hf := wheatstone_fixed_point_factorization p
    rw [h, sub_self] at hf
    have htwo : 2 * p - 1 = 0 := by
      rcases mul_eq_zero.mp hf.symm with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact False.elim ((mul_pos hp (sub_pos.mpr hp')).ne' h)
        · exact h
      · exact False.elim (hlast.ne' h)
    linarith
  · intro h
    rw [h, wheatstone_reliability]
    norm_num

end Universality
