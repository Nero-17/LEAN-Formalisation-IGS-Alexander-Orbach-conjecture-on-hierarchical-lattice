import Universality.Percolation.ClusterNumberIteration
import Universality.Percolation.ClusterNumberSeries
import Universality.Graph.VolumeLimit

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem unitReliability_iterate_val (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    (R.unitReliability^[n] p).val = R.reliability^[n] p.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change R.reliability (R.unitReliability^[n] p).val = _
    rw [ih]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem generation_expectedClusterNumber_normalized (rule : Rule) (n : ℕ) (p : ℝ)
    (hedges : 0 < rule.edges) :
    (rule.generation n).network.expectedClusterNumber p / (rule.edges : ℝ) ^ (n + 1) =
      (∑ k ∈ Finset.range (n + 1), (1 / (rule.edges : ℝ)) ^ (k + 1) *
        rule.network.expectedInternalClusterNumber (rule.network.reliability^[k] p)) +
      (2 - rule.network.reliability^[n + 1] p) * (1 / (rule.edges : ℝ)) ^ (n + 1) := by
  have hm : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hedges)
  rw [rule.generation_expectedClusterNumber]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (rule.edges : ℝ) ^ (n - k) / (rule.edges : ℝ) ^ (n + 1) =
        (1 / (rule.edges : ℝ)) ^ (k + 1) := by
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [one_div_pow]
    apply (div_eq_div_iff (pow_ne_zero _ hm) (pow_ne_zero _ hm)).mpr
    rw [← pow_add, one_mul]
    congr 1
    omega
  calc
    _ = (∑ k ∈ Finset.range (n + 1),
          ((rule.edges : ℝ) ^ (n - k) / (rule.edges : ℝ) ^ (n + 1)) *
            rule.network.expectedInternalClusterNumber (rule.network.reliability^[k] p)) +
          (2 - rule.network.reliability^[n + 1] p) / (rule.edges : ℝ) ^ (n + 1) := by
      conv_rhs => simp only [div_mul_eq_mul_div]; rw [← Finset.sum_div]
      ring
    _ = _ := by
      rw [one_div_pow, div_eq_mul_one_div (2 - _)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [hterm k hk]

end
end Universality.Rule
