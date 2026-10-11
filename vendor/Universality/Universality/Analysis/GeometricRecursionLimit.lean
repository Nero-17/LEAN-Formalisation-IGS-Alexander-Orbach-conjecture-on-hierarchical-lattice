import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem positive_geometric_recursion_limit (sequence error : ℕ → ℝ) (growth : ℝ)
    (hgrowth : 1 ≤ growth) (hinitial : 0 < sequence 0)
    (hlower : ∀ n, growth * sequence n ≤ sequence (n + 1))
    (hupper : ∀ n, sequence (n + 1) ≤ growth * sequence n + error n)
    (hsummable : Summable error) :
    ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun n : ℕ => sequence n / growth ^ n) atTop (𝓝 limit) := by
  have hgrowthpos : 0 < growth := lt_of_lt_of_le zero_lt_one hgrowth
  have herr (n : ℕ) : 0 ≤ error n := by linarith [hlower n, hupper n]
  have hdifference (n : ℕ) : sequence (n + 1) / growth ^ (n + 1) - sequence n / growth ^ n =
      (sequence (n + 1) - growth * sequence n) / growth ^ (n + 1) := by
    rw [pow_succ]
    field_simp [hgrowthpos.ne']
  have hnonneg (n : ℕ) : 0 ≤ sequence (n + 1) / growth ^ (n + 1) - sequence n / growth ^ n := by
    rw [hdifference]
    exact div_nonneg (sub_nonneg.mpr (hlower n)) (pow_pos hgrowthpos _).le
  have hbound (n : ℕ) : sequence (n + 1) / growth ^ (n + 1) - sequence n / growth ^ n ≤ error n := by
    rw [hdifference]
    calc
      _ ≤ error n / growth ^ (n + 1) := div_le_div_of_nonneg_right (by linarith [hupper n])
        (pow_pos hgrowthpos _).le
      _ ≤ error n := div_le_self (herr n) (one_le_pow₀ hgrowth)
  have hs := hsummable.of_nonneg_of_le hnonneg hbound
  refine ⟨sequence 0 + ∑' n : ℕ,
    (sequence (n + 1) / growth ^ (n + 1) - sequence n / growth ^ n),
    add_pos_of_pos_of_nonneg hinitial (tsum_nonneg hnonneg), ?_⟩
  have htel (n : ℕ) : (∑ k ∈ Finset.range n,
      (sequence (k + 1) / growth ^ (k + 1) - sequence k / growth ^ k)) =
      sequence n / growth ^ n - sequence 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hlimit := hs.hasSum.tendsto_sum_nat.const_add (sequence 0)
  simp only [htel, add_sub_cancel] at hlimit
  exact hlimit

end
end Universality
