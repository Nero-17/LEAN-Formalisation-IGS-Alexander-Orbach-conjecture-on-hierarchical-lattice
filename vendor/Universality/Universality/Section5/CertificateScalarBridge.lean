import Universality.Section5.AllocationRealisation

namespace Universality.Section5
noncomputable section

theorem thermalMoment_cast (words : List (List Bool)) (allocation : List Bool → ℕ) :
    (((words.map (fun word => allocation word * 6 ^ zeroCount word)).sum : ℕ) : ℝ) =
      (words.map (fun word => (allocation word : ℝ) * 6 ^ zeroCount word)).sum := by
  induction words with
  | nil => simp
  | cons word words induction_hypothesis => simp [induction_hypothesis]

theorem thermalResponse_of_integer_identity (n base : ℕ) (moment : ℕ)
    (identity : 8 ^ (n + 1) * base ^ 70 = 8 * 13 ^ n + 5 * moment) :
    (13 / 8 : ℝ) ^ n + (5 / 8 : ℝ) * (1 / 8 : ℝ) ^ n * moment = (base : ℝ) ^ 70 := by
  have identity_real : (8 : ℝ) ^ (n + 1) * (base : ℝ) ^ 70 = 8 * 13 ^ n + 5 * moment := by
    exact_mod_cast identity
  have nonzero : (8 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (mul_right_cancel₀ nonzero)
  calc
    ((13 / 8 : ℝ) ^ n + (5 / 8 : ℝ) * (1 / 8 : ℝ) ^ n * moment) * 8 ^ (n + 1) =
        8 * 13 ^ n + 5 * moment := by
      rw [div_pow, one_div_pow, pow_succ]
      field_simp
      <;> ring
    _ = (base : ℝ) ^ 70 * 8 ^ (n + 1) := by rw [← identity_real, mul_comm]

theorem allocation_derivative_of_certificate (n base : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word)
    (thermal : 8 ^ (n + 1) * base ^ 70 = 8 * 13 ^ n +
      5 * ((binaryWords n).map (fun word => allocation word * 6 ^ zeroCount word)).sum) :
    deriv (allocatedExpression n (allocationDecoration allocation)).rule.network.reliability (1 / 2) =
      (base : ℝ) ^ 70 := by
  rw [allocation_derivative n allocation capacity, ← thermalMoment_cast]
  exact thermalResponse_of_integer_identity n base _ thermal

end
end Universality.Section5
