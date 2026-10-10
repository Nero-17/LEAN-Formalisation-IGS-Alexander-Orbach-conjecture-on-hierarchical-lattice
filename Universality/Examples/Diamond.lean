import Universality.Percolation.CountingPolynomials
import Universality.Percolation.ReliabilityDerivative
import Universality.Matrix.CriticalCharacteristic
import Mathlib.Tactic.FinCases

namespace Universality
noncomputable section
set_option maxHeartbeats 0
open FiniteNetwork Polynomial Matrix

/-- The four-edge diamond in Section 2, with the same terminal convention
as the Wheatstone network but without its central edge. -/
def diamondNetwork : FiniteNetwork 4 4 where
  endpoint := ![(0, 2), (2, 1), (0, 3), (3, 1)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

def diamondCountingTable : LiveState → LiveState → Fin 5 → ℕ
  | .connected, .connected => fun k => match k.val with | 2 => 4 | 3 => 12 | 4 => 4 | _ => 0
  | .connected, .both => fun k => if k.val = 3 then 4 else 0
  | .connected, .single => fun k => if k.val = 2 then 4 else 0
  | .both, .connected | .both, .both => fun k => match k.val with | 1 => 4 | 2 => 8 | _ => 0
  | .both, .single => fun k => match k.val with | 0 => 4 | 1 => 8 | _ => 0
  | .single, .connected => fun k => match k.val with | 1 => 2 | 2 => 4 | _ => 0
  | .single, .both => fun _ => 0
  | .single, .single => fun k => match k.val with | 0 => 2 | 1 => 8 | 2 => 8 | _ => 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem diamond_exact_counts :
    (∀ k : Fin 5, diamondNetwork.crossingCountBySize k = ![0, 0, 2, 4, 1] k) ∧
    (∀ σ τ (k : Fin 5), diamondNetwork.liveCountBySize σ τ k = diamondCountingTable σ τ k) := by
  decide

theorem diamond_reliabilityPolynomial :
    diamondNetwork.reliabilityPolynomial = 2 * X ^ 2 - X ^ 4 := by
  rw [reliabilityPolynomial_bernstein]
  have h0 : diamondNetwork.crossingCountBySize 0 = 0 := diamond_exact_counts.1 0
  have h1 : diamondNetwork.crossingCountBySize 1 = 0 := diamond_exact_counts.1 1
  have h2 : diamondNetwork.crossingCountBySize 2 = 2 := diamond_exact_counts.1 2
  have h3 : diamondNetwork.crossingCountBySize 3 = 4 := diamond_exact_counts.1 3
  have h4 : diamondNetwork.crossingCountBySize 4 = 1 := diamond_exact_counts.1 4
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4]
  ring

theorem diamond_reliability (p : ℝ) :
    diamondNetwork.reliability p = 2 * p ^ 2 - p ^ 4 := by
  rw [← diamondNetwork.reliabilityPolynomial_eval, diamond_reliabilityPolynomial]
  simp

def diamondCountingFormula : LiveState → LiveState → Polynomial ℤ
  | .connected, .connected => 4 * X ^ 2 * (1 + X - X ^ 2)
  | .connected, .both => 4 * X ^ 3 * (1 - X)
  | .connected, .single => 4 * X ^ 2 * (1 - X) ^ 2
  | .both, .connected | .both, .both => 4 * X * (1 - X) ^ 2 * (1 + X)
  | .both, .single => 4 * (1 - X) ^ 3 * (1 + X)
  | .single, .connected => 2 * X * (1 - X) ^ 2 * (1 + X)
  | .single, .both => 0
  | .single, .single => 2 * (1 - X ^ 2) ^ 2

theorem diamond_countingPolynomial (σ τ : LiveState) :
    diamondNetwork.countingPolynomial σ τ = diamondCountingFormula σ τ := by
  rw [countingPolynomial_bernstein]
  have h0 : diamondNetwork.liveCountBySize σ τ 0 = diamondCountingTable σ τ 0 :=
    diamond_exact_counts.2 σ τ 0
  have h1 : diamondNetwork.liveCountBySize σ τ 1 = diamondCountingTable σ τ 1 :=
    diamond_exact_counts.2 σ τ 1
  have h2 : diamondNetwork.liveCountBySize σ τ 2 = diamondCountingTable σ τ 2 :=
    diamond_exact_counts.2 σ τ 2
  have h3 : diamondNetwork.liveCountBySize σ τ 3 = diamondCountingTable σ τ 3 :=
    diamond_exact_counts.2 σ τ 3
  have h4 : diamondNetwork.liveCountBySize σ τ 4 = diamondCountingTable σ τ 4 :=
    diamond_exact_counts.2 σ τ 4
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3, h4]
  cases σ <;> cases τ <;>
    norm_num [diamondCountingTable, diamondCountingFormula, Matrix.cons_val] <;> ring

def diamondMassFormula (p : ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected => 4 * (1 + p - p ^ 2) / (2 - p ^ 2)
  | .connected, .both => 4 * p * (1 - p) / (2 - p ^ 2)
  | .connected, .single => 4 * (1 - p) ^ 2 / (2 - p ^ 2)
  | .both, .connected | .both, .both => 4 * p / (1 + p)
  | .both, .single => 4 * (1 - p) / (1 + p)
  | .single, .connected => 2 * p / (1 + p)
  | .single, .both => 0
  | .single, .single => 2

theorem diamond_massMatrix (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    diamondNetwork.massMatrix p = diamondMassFormula p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hm : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp')
  have hplus : 1 + p ≠ 0 := by linarith
  have hp2 : p ^ 2 < 1 := by nlinarith [mul_pos hp (sub_pos.mpr hp')]
  have htwo : 2 - p ^ 2 ≠ 0 := by linarith
  have hd : 1 - (2 * p ^ 2 - p ^ 4) = (1 - p) ^ 2 * (1 + p) ^ 2 := by ring
  have hc : 2 * p ^ 2 - p ^ 4 = p ^ 2 * (2 - p ^ 2) := by ring
  have hdenom : 1 - (2 * p ^ 2 - p ^ 4) ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (pow_ne_zero _ hm) (pow_ne_zero _ hplus)
  have hdenom' : 1 - p ^ 2 * 2 + p ^ 4 ≠ 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hp2)]
  ext σ τ
  rw [massMatrix_eq_countingPolynomial, diamond_countingPolynomial, diamond_reliability]
  cases σ <;> cases τ <;>
    simp only [diamondCountingFormula, diamondMassFormula, eval₂_mul, eval₂_pow,
      eval₂_sub, eval₂_add, eval₂_X, eval₂_ofNat, eval₂_zero, eval₂_one,
      ite_true, ite_false, reduceCtorEq] <;>
    simp only [hc] <;>
    field_simp [hp0, hm, hplus, htwo, hdenom, hdenom'] <;> ring_nf <;>
    nlinarith [mul_inv_cancel₀ hdenom']

end
end Universality
