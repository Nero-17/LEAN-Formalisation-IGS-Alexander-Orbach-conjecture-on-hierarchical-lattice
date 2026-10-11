import Universality.Examples.TieGemSimilarity

namespace Universality
noncomputable section
open FiniteNetwork Polynomial Matrix
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def triangleCountingTable : LiveState → LiveState → Fin 4 → ℕ
  | .connected, .connected => ![0, 1, 6, 3]
  | .connected, .both => ![0, 0, 3, 0]
  | .connected, .single => ![0, 2, 0, 0]
  | .both, .connected => ![0, 2, 0, 0]
  | .both, .both => ![1, 4, 0, 0]
  | .both, .single => ![2, 0, 0, 0]
  | .single, .connected => ![0, 1, 0, 0]
  | .single, .both => ![0, 0, 0, 0]
  | .single, .single => ![2, 4, 0, 0]

theorem triangle_live_counts :
    ∀ parent child (k : Fin 4), triangleNetwork.liveCountBySize parent child k =
      triangleCountingTable parent child k := by decide

def triangleCountingFormula : LiveState → LiveState → Polynomial ℤ
  | .connected, .connected => X + 4 * X ^ 2 - 2 * X ^ 3
  | .connected, .both => 3 * X ^ 2 * (1 - X)
  | .connected, .single => 2 * X * (1 - X) ^ 2
  | .both, .connected => 2 * X * (1 - X) ^ 2
  | .both, .both => (1 - X) ^ 2 * (1 + 3 * X)
  | .both, .single => 2 * (1 - X) ^ 3
  | .single, .connected => X * (1 - X) ^ 2
  | .single, .both => 0
  | .single, .single => 2 * (1 - X) ^ 2 * (1 + X)

theorem triangle_countingPolynomial (parent child : LiveState) :
    triangleNetwork.countingPolynomial parent child = triangleCountingFormula parent child := by
  rw [countingPolynomial_bernstein]
  have h0 : triangleNetwork.liveCountBySize parent child 0 = triangleCountingTable parent child 0 := triangle_live_counts parent child 0
  have h1 : triangleNetwork.liveCountBySize parent child 1 = triangleCountingTable parent child 1 := triangle_live_counts parent child 1
  have h2 : triangleNetwork.liveCountBySize parent child 2 = triangleCountingTable parent child 2 := triangle_live_counts parent child 2
  have h3 : triangleNetwork.liveCountBySize parent child 3 = triangleCountingTable parent child 3 := triangle_live_counts parent child 3
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3]
  cases parent <;> cases child <;>
    norm_num [triangleCountingTable, triangleCountingFormula, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

def triangleMassFormula (p : ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected => (1 + 4 * p - 2 * p ^ 2) / (1 + p - p ^ 2)
  | .connected, .both => 3 * p * (1 - p) / (1 + p - p ^ 2)
  | .connected, .single => 2 * (1 - p) ^ 2 / (1 + p - p ^ 2)
  | .both, .connected => 2 * p / (1 + p)
  | .both, .both => (1 + 3 * p) / (1 + p)
  | .both, .single => 2 * (1 - p) / (1 + p)
  | .single, .connected => p / (1 + p)
  | .single, .both => 0
  | .single, .single => 2

theorem triangle_massMatrix (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    triangleNetwork.massMatrix p = triangleMassFormula p := by
  have hp0 : p ≠ 0 := hp.ne'
  have hminus : 1 - p ≠ 0 := (sub_pos.mpr hp').ne'
  have hplus : 1 + p ≠ 0 := by linarith
  have hquad : 1 + p - p ^ 2 ≠ 0 := by nlinarith [mul_pos hp (sub_pos.mpr hp')]
  have hcross : p + p ^ 2 - p ^ 3 ≠ 0 := by
    have : p + p ^ 2 - p ^ 3 = p * (1 + p - p ^ 2) := by ring
    rw [this]; exact mul_ne_zero hp0 hquad
  have hdenom : 1 - (p + p ^ 2 - p ^ 3) ≠ 0 := by
    have : 1 - (p + p ^ 2 - p ^ 3) = (1 - p) ^ 2 * (1 + p) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hminus) hplus
  have hdenom' : 1 - p - p ^ 2 + p ^ 3 ≠ 0 := by
    convert hdenom using 1 <;> ring
  ext parent child
  rw [massMatrix_eq_countingPolynomial, triangle_countingPolynomial, triangle_reliability]
  cases parent <;> cases child <;>
    simp only [triangleCountingFormula, triangleMassFormula, eval₂_mul, eval₂_pow,
      eval₂_sub, eval₂_add, eval₂_X, eval₂_ofNat, eval₂_zero, eval₂_one,
      ite_true, ite_false, reduceCtorEq] <;>
    field_simp [hp0, hplus, hminus, hquad, hcross, hdenom, hdenom'] <;>
    ring_nf <;> field_simp [hdenom'] <;> ring

end
end Universality
