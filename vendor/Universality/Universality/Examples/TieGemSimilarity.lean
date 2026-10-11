import Universality.Examples.TieGemData
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Universality
noncomputable section
open FiniteNetwork Polynomial Matrix
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def twoEdgePathCountingTable : LiveState → LiveState → Fin 3 → ℕ
  | .connected, .connected => fun k => if k.val = 2 then 2 else 0
  | .both, .connected | .both, .both => fun k => if k.val = 1 then 2 else 0
  | .both, .single => fun k => if k.val = 0 then 2 else 0
  | .single, .connected => fun k => if k.val = 1 then 1 else 0
  | .single, .single => fun k => match k.val with | 0 => 1 | 1 => 2 | _ => 0
  | _, _ => fun _ => 0

theorem twoEdgePath_live_counts :
    ∀ parent child (k : Fin 3), twoEdgePathNetwork.liveCountBySize parent child k =
      twoEdgePathCountingTable parent child k := by decide

def twoEdgePathCountingFormula : LiveState → LiveState → Polynomial ℤ
  | .connected, .connected => 2 * X ^ 2
  | .both, .connected | .both, .both => 2 * X * (1 - X)
  | .both, .single => 2 * (1 - X) ^ 2
  | .single, .connected => X * (1 - X)
  | .single, .single => 1 - X ^ 2
  | _, _ => 0

theorem twoEdgePath_countingPolynomial (parent child : LiveState) :
    twoEdgePathNetwork.countingPolynomial parent child = twoEdgePathCountingFormula parent child := by
  rw [countingPolynomial_bernstein]
  have h0 : twoEdgePathNetwork.liveCountBySize parent child 0 = twoEdgePathCountingTable parent child 0 := twoEdgePath_live_counts parent child 0
  have h1 : twoEdgePathNetwork.liveCountBySize parent child 1 = twoEdgePathCountingTable parent child 1 := twoEdgePath_live_counts parent child 1
  have h2 : twoEdgePathNetwork.liveCountBySize parent child 2 = twoEdgePathCountingTable parent child 2 := twoEdgePath_live_counts parent child 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2]
  cases parent <;> cases child <;>
    norm_num [twoEdgePathCountingTable, twoEdgePathCountingFormula, Matrix.cons_val] <;> ring

def twoEdgePathMassFormula (p : ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected => 2
  | .both, .connected | .both, .both => 2 * p / (1 + p)
  | .both, .single => 2 * (1 - p) / (1 + p)
  | .single, .connected => p / (1 + p)
  | .single, .single => 1
  | _, _ => 0

theorem twoEdgePath_massMatrix (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    twoEdgePathNetwork.massMatrix p = twoEdgePathMassFormula p := by
  have hp0 : p ≠ 0 := hp.ne'
  have hplus : 1 + p ≠ 0 := by linarith
  have hsquare : p ^ 2 < 1 := by nlinarith [mul_pos hp (sub_pos.mpr hp')]
  have hdenom : 1 - p ^ 2 ≠ 0 := by linarith
  ext parent child
  rw [massMatrix_eq_countingPolynomial, twoEdgePath_countingPolynomial, twoEdgePath_reliability]
  cases parent <;> cases child <;>
    simp only [twoEdgePathCountingFormula, twoEdgePathMassFormula, eval₂_mul, eval₂_pow,
      eval₂_sub, eval₂_add, eval₂_X, eval₂_ofNat, eval₂_zero, eval₂_one,
      ite_true, ite_false, reduceCtorEq] <;>
    field_simp [hp0, hplus, hdenom] <;> ring

theorem twoEdgePath_massMatrix_det (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (twoEdgePathNetwork.massMatrix p).det = 4 * p / (1 + p) := by
  rw [twoEdgePath_massMatrix p hp hp', ← Matrix.det_submatrix_equiv_self liveStateEnumeration,
    Matrix.det_fin_three]
  simp [Matrix.submatrix, liveStateEnumeration, twoEdgePathMassFormula]
  ring

theorem tie_gem_explicit_similarity (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (twoEdgePathNetwork.massMatrix p)⁻¹ * tieRule.network.massMatrix (p ^ 2) *
      twoEdgePathNetwork.massMatrix p = gemRule.network.massMatrix p := by
  have hprob : 0 < twoEdgePathNetwork.reliability p := by rw [twoEdgePath_reliability]; positivity
  have hprob' : twoEdgePathNetwork.reliability p < 1 := twoEdgePathNetwork.reliability_lt_one hp hp'
  have hfixed' : triangleNetwork.reliability (p ^ 2) = p := by
    simpa only [gemRule, Rule.mul_reliability, triangleRule, twoEdgePathRule,
      twoEdgePath_reliability] using hfixed
  have hgem := Rule.mul_massMatrix triangleRule twoEdgePathRule p hprob hprob'
    twoEdgePathTerminalSymmetry (by decide) (by decide)
  have htie := Rule.mul_massMatrix twoEdgePathRule triangleRule (p ^ 2)
    (by change 0 < triangleNetwork.reliability (p ^ 2); rwa [hfixed'])
    (by change triangleNetwork.reliability (p ^ 2) < 1; rwa [hfixed'])
    triangleTerminalSymmetry (by decide) (by decide)
  change tieRule.network.massMatrix (p ^ 2) =
    twoEdgePathNetwork.massMatrix (triangleNetwork.reliability (p ^ 2)) *
      triangleNetwork.massMatrix (p ^ 2) at htie
  rw [hfixed'] at htie
  change gemRule.network.massMatrix p = triangleNetwork.massMatrix
    (twoEdgePathNetwork.reliability p) * twoEdgePathNetwork.massMatrix p at hgem
  rw [twoEdgePath_reliability] at hgem
  have hunit : IsUnit (twoEdgePathNetwork.massMatrix p).det := by
    rw [twoEdgePath_massMatrix_det p hp hp', isUnit_iff_ne_zero]
    exact (div_pos (mul_pos (by norm_num) hp) (by linarith)).ne'
  rw [htie, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul, hgem]

end
end Universality
