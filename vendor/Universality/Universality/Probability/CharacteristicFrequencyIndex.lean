import Universality.Probability.L2Characteristic

namespace Universality
noncomputable section

/-- The first scale at which a frequency reaches one lies in the fixed
annulus [1, radius]. This discrete selection avoids logarithms and floors. -/
theorem exists_frequency_annulus_depth (frequency radius : ℝ) (minimum maximum : ℕ)
    (hradius : 1 < radius) (hdepth : minimum ≤ maximum)
    (hlow : frequency * radius ^ minimum < 1)
    (hhigh : 1 ≤ frequency * radius ^ maximum) :
    ∃ depth : ℕ, minimum ≤ depth ∧ depth ≤ maximum ∧
      1 ≤ frequency * radius ^ depth ∧ frequency * radius ^ depth ≤ radius := by
  classical
  have hexists : ∃ depth : ℕ, minimum ≤ depth ∧ 1 ≤ frequency * radius ^ depth :=
    ⟨maximum, hdepth, hhigh⟩
  let depth := Nat.find hexists
  have hspec : minimum ≤ depth ∧ 1 ≤ frequency * radius ^ depth := Nat.find_spec hexists
  have hupper : depth ≤ maximum := Nat.find_min' hexists ⟨hdepth, hhigh⟩
  have hstrict : minimum < depth := by
    apply lt_of_le_of_ne hspec.1
    intro heq
    have hvalue := hspec.2
    rw [← heq] at hvalue
    exact (not_le_of_gt hlow) hvalue
  have hprevious : frequency * radius ^ (depth - 1) < 1 := by
    by_contra hnot
    have hpreviousDepth : depth - 1 < depth := by omega
    exact Nat.find_min hexists hpreviousDepth ⟨by omega, le_of_not_gt hnot⟩
  refine ⟨depth, hspec.1, hupper, hspec.2, ?_⟩
  calc
    frequency * radius ^ depth = frequency * radius ^ (depth - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ depth by omega)]
    _ = (frequency * radius ^ (depth - 1)) * radius := by rw [pow_succ]; ring
    _ ≤ 1 * radius := mul_le_mul_of_nonneg_right hprevious.le (zero_lt_one.trans hradius).le
    _ = radius := one_mul _

end
end Universality
