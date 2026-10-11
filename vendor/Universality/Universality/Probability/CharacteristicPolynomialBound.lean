import Universality.Probability.CharacteristicPowerDecay

namespace Universality
noncomputable section

/-- A discrete iterated-power frequency cover implies every polynomial bound. -/
theorem characteristic_polynomial_bound (radius bound : ℝ) (degree order : ℕ)
    (hradius : 0 < radius) (hbound0 : 0 ≤ bound) (hbound1 : bound < 1)
    (hdegree : 2 ≤ degree) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ value frequency : ℝ,
      0 ≤ value →
      (∃ k : ℕ, value ≤ bound ^ (degree ^ k) ∧
        |frequency| ≤ Real.pi * radius ^ (k + 1)) →
      value * |frequency| ^ order ≤ constant := by
  have hsummable := summable_geometric_mul_iterated_power bound (radius ^ order) degree
    hbound0 hbound1 (pow_pos hradius _) hdegree
  let constant := (Real.pi * radius) ^ order *
    ∑' k : ℕ, bound ^ (degree ^ k) * (radius ^ order) ^ k
  have hterm0 (k : ℕ) : 0 ≤ bound ^ (degree ^ k) * (radius ^ order) ^ k :=
    mul_nonneg (pow_nonneg hbound0 _) (pow_nonneg (pow_nonneg hradius.le _) _)
  refine ⟨constant, mul_nonneg (pow_nonneg (mul_pos Real.pi_pos hradius).le _)
    (tsum_nonneg hterm0), ?_⟩
  intro value frequency hvalue hexists
  obtain ⟨k, hk, hfrequency⟩ := hexists
  calc
    value * |frequency| ^ order ≤
        bound ^ (degree ^ k) * (Real.pi * radius ^ (k + 1)) ^ order :=
      mul_le_mul hk (pow_le_pow_left₀ (abs_nonneg _) hfrequency _) (pow_nonneg (abs_nonneg _) _) (pow_nonneg hbound0 _)
    _ = (Real.pi * radius) ^ order * (bound ^ (degree ^ k) * (radius ^ order) ^ k) := by
      have heq : (radius ^ k) ^ order = (radius ^ order) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      simp only [pow_succ, mul_pow, heq]
      ring
    _ ≤ constant := mul_le_mul_of_nonneg_left
      (hsummable.le_tsum k (fun i _ => hterm0 i)) (pow_nonneg (mul_pos Real.pi_pos hradius).le _)

end
end Universality
