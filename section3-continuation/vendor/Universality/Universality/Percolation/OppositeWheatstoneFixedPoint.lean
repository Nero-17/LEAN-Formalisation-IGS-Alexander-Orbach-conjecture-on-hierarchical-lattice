import Universality.Percolation.OppositeWheatstoneReliability

namespace Universality
open FiniteNetwork Polynomial

theorem oppositeWheatstone_fixed_point_factorization (p : ℝ) :
    oppositeWheatstoneNetwork.reliability p - p =
      p * (1 - p) * (2 * p - 1) *
        (1 + 3 * (p * (1 - p)) + 5 * (p * (1 - p)) ^ 2 +
          6 * (p * (1 - p)) ^ 3 + 7 * (p * (1 - p)) ^ 4 + 4 * (p * (1 - p)) ^ 5) := by
  rw [← oppositeWheatstoneNetwork.reliabilityPolynomial_eval p,
    oppositeWheatstone_reliabilityPolynomial]
  norm_num
  ring

theorem oppositeWheatstone_unique_interior_fixed_point {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    oppositeWheatstoneNetwork.reliability p = p ↔ p = 1 / 2 := by
  have hsub : 0 < 1 - p := sub_pos.mpr hp'
  have hlast : 0 < 1 + 3 * (p * (1 - p)) + 5 * (p * (1 - p)) ^ 2 +
      6 * (p * (1 - p)) ^ 3 + 7 * (p * (1 - p)) ^ 4 + 4 * (p * (1 - p)) ^ 5 := by positivity
  have hfactor := oppositeWheatstone_fixed_point_factorization p
  constructor
  · intro h
    rw [h, sub_self] at hfactor
    have hmiddle : 2 * p - 1 = 0 := by
      rcases mul_eq_zero.mp hfactor.symm with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact False.elim ((mul_pos hp hsub).ne' h)
        · exact h
      · exact False.elim (hlast.ne' h)
    linarith
  · intro h
    rw [h] at hfactor ⊢
    norm_num at hfactor
    linarith

end Universality
