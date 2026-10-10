import Universality.Probability.CharacteristicFrequencyIndex

namespace Universality
noncomputable section

/-- Two frequency gaps and the finite-depth contraction cover the whole
expanding fundamental interval, using only an integer first-crossing scale. -/
theorem characteristic_frequency_cover {State : Type*}
    (modulus : ℕ → State → ℝ → ℝ) (radius bound : ℝ) (degree depth : ℕ)
    (hradius : 1 < radius) (hdepth : 1 ≤ depth)
    (hbase : ∀ state u, 1 ≤ |u| * radius ^ depth → |u| ≤ Real.pi →
      modulus 1 state u ≤ bound)
    (hannulus : ∀ m ≥ depth, ∀ state u,
      1 ≤ |u| * radius ^ m → |u| * radius ^ m ≤ radius → modulus m state u ≤ bound)
    (hiterate : ∀ m u, (∀ state, modulus m state u ≤ bound) →
      ∀ k state, modulus (m + k) state u ≤ bound ^ (degree ^ k))
    (n : ℕ) (hn : depth ≤ n) (state : State) (u : ℝ)
    (hu : 1 ≤ |u| * radius ^ n) (hpi : |u| ≤ Real.pi) :
    ∃ k : ℕ, modulus n state u ≤ bound ^ (degree ^ k) ∧
      |u| * radius ^ n ≤ Real.pi * radius ^ (k + 1) := by
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  by_cases hhigh : 1 ≤ |u| * radius ^ depth
  · refine ⟨n - 1, ?_, ?_⟩
    · have h := hiterate 1 u (fun child => hbase child u hhigh hpi) (n - 1) state
      simpa only [Nat.add_sub_of_le (hdepth.trans hn)] using h
    · simpa only [Nat.sub_add_cancel (hdepth.trans hn)] using
        mul_le_mul_of_nonneg_right hpi (pow_nonneg hradius0.le n)
  · obtain ⟨m, hm, hmn, hfirst, hlast⟩ := exists_frequency_annulus_depth |u| radius
      depth n hradius hn (lt_of_not_ge hhigh) hu
    refine ⟨n - m, ?_, ?_⟩
    · have h := hiterate m u (fun child => hannulus m hm child u hfirst hlast) (n - m) state
      simpa only [Nat.add_sub_of_le hmn] using h
    · calc
        |u| * radius ^ n = (|u| * radius ^ m) * radius ^ (n - m) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hmn]
        _ ≤ radius * radius ^ (n - m) :=
          mul_le_mul_of_nonneg_right hlast (pow_nonneg hradius0.le _)
        _ = radius ^ (n - m + 1) := by rw [pow_succ]; ring
        _ ≤ Real.pi * radius ^ (n - m + 1) := by
          nlinarith [Real.two_le_pi, pow_pos hradius0 (n - m + 1)]

end
end Universality
