import Universality.Section5.AllocationProjection

namespace Universality.Section5
noncomputable section

theorem allocationDecoration_filter (allocation : List Bool → ℕ) (word : List Bool) :
    (projectedAddresses word).filter (allocationDecoration allocation) =
      (projectedAddresses word).take (allocation word) := by
  rw [(projectedAddresses_nodup word).take_eq_filter_mem]
  apply List.filter_congr
  intro address member
  have projection := (mem_projectedAddresses address word).mp member
  simp [allocationDecoration, projection]

theorem allocationDecoration_count (allocation : List Bool → ℕ) (word : List Bool)
    (capacity : allocation word ≤ 2 ^ zeroCount word) :
    ((projectedAddresses word).filter (allocationDecoration allocation)).length = allocation word := by
  rw [allocationDecoration_filter, List.length_take, projectedAddresses_length,
    Nat.min_eq_left capacity]

private theorem sum_list_indicator {α R : Type*} [AddCommMonoid R]
    (addresses : List α) (selected : α → Bool) (value : R) :
    (addresses.map (fun address => if selected address then value else 0)).sum =
      (addresses.filter selected).length • value := by
  induction addresses with
  | nil => simp
  | cons address addresses induction_hypothesis =>
      cases chosen : selected address <;> simp [chosen, induction_hypothesis, add_nsmul, add_comm]

theorem allocationDecoration_projected_sum {R : Type*} [AddCommMonoid R]
    (allocation : List Bool → ℕ) (word : List Bool)
    (capacity : allocation word ≤ 2 ^ zeroCount word) (response : List Bool → R) :
    ((projectedAddresses word).map (fun address => if allocationDecoration allocation address then
      response (projectedAddress address) else 0)).sum = allocation word • response word := by
  have same : ((projectedAddresses word).map (fun address => if allocationDecoration allocation address then
      response (projectedAddress address) else 0)) =
      (projectedAddresses word).map (fun address => if allocationDecoration allocation address then
        response word else 0) := by
    apply List.map_congr_left
    intro address member
    rw [(mem_projectedAddresses address word).mp member]
  rw [same, sum_list_indicator, allocationDecoration_count allocation word capacity]

theorem decoratedLeafWeight_from_allocation {R : Type*} [Semiring R]
    (outer central : R) (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word) :
    decoratedLeafWeight outer central n (allocationDecoration allocation) =
      ((binaryWords n).map (fun word => allocation word • wordProduct outer central word)).sum := by
  rw [decoratedLeafWeight_eq_sum]
  simp_rw [addressWeight_eq_wordProduct]
  rw [sum_ternaryAddresses_by_projection]
  apply congrArg List.sum
  apply List.map_congr_left
  intro word member
  exact allocationDecoration_projected_sum allocation word (capacity word member) _

theorem wordProduct_outer_nat (outer : ℕ) (word : List Bool) :
    wordProduct outer 1 word = outer ^ zeroCount word := by
  induction word with
  | nil => simp [wordProduct, zeroCount]
  | cons bit word induction_hypothesis =>
      cases bit <;> simp [wordProduct, induction_hypothesis, pow_succ, Nat.mul_comm]

theorem allocation_edges (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word) :
    (allocatedExpression n (allocationDecoration allocation)).rule.edges =
      5 ^ n + 4 * ((binaryWords n).map (fun word => allocation word * 2 ^ zeroCount word)).sum := by
  rw [allocatedExpression_edges, decoratedLeafWeight_from_allocation _ _ _ _ capacity]
  simp only [wordProduct_outer_nat, nsmul_eq_mul, Nat.cast_id]

theorem wordProduct_thermal (word : List Bool) :
    wordProduct (3 / 4 : ℝ) (1 / 8) word = (1 / 8 : ℝ) ^ word.length * 6 ^ zeroCount word := by
  induction word with
  | nil => simp [wordProduct, zeroCount]
  | cons bit word induction_hypothesis =>
      cases bit <;> simp only [wordProduct, induction_hypothesis, List.length_cons,
        zeroCount_false_cons, zeroCount_true_cons, pow_succ] <;> ring

theorem allocation_derivative (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word) :
    deriv (allocatedExpression n (allocationDecoration allocation)).rule.network.reliability (1 / 2) =
      (13 / 8 : ℝ) ^ n + (5 / 8 : ℝ) * (1 / 8 : ℝ) ^ n *
        ((binaryWords n).map (fun word => (allocation word : ℝ) * 6 ^ zeroCount word)).sum := by
  rw [allocatedExpression_derivative, decoratedLeafWeight_from_allocation _ _ _ _ capacity]
  have weighted : ((binaryWords n).map
      (fun word => allocation word • wordProduct (3 / 4 : ℝ) (1 / 8) word)).sum =
      (1 / 8 : ℝ) ^ n * ((binaryWords n).map
        (fun word => (allocation word : ℝ) * 6 ^ zeroCount word)).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro word member
    rw [wordProduct_thermal, word_length_of_mem_binaryWords member, nsmul_eq_mul]
    ring
  rw [weighted]
  ring

end
end Universality.Section5
