import Universality.Graph.Section5Classical
import Universality.Section5.AllocationScalars
import Universality.Section5.AllocationRealisation

set_option backward.isDefEq.respectTransparency false

namespace Universality.Section5
noncomputable section
open FiniteNetwork

def singleEdgeDistanceCertificate : singleEdgeNetwork.DistanceCertificate where
  length := 1
  height := ![0, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := .cons (by decide : singleEdgeNetwork.fullGraph.Adj 0 1) .nil
  walk_length := rfl

theorem singleEdgeRule_distance :
    singleEdgeRule.network.fullGraph.dist singleEdgeRule.network.source singleEdgeRule.network.target = 1 :=
  singleEdgeDistanceCertificate.distance_eq _

theorem decoratedOuterLeaves_bound (n : ℕ) (decorated : List (Fin 3) → Bool) :
    decoratedLeafWeight (1 : ℕ) 0 n decorated ≤ 2 ^ n := by
  induction n generalizing decorated with
  | zero => cases value : decorated [] <;> simp [decoratedLeafWeight, value]
  | succ n induction_hypothesis =>
      have first := induction_hypothesis (fun address => decorated (0 :: address))
      have second := induction_hypothesis (fun address => decorated (1 :: address))
      simp only [decoratedLeafWeight, one_mul, zero_mul, add_zero, pow_succ]
      omega

theorem allocatedExpression_distance (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).rule.network.fullGraph.dist
      (allocatedExpression n decorated).rule.network.source
      (allocatedExpression n decorated).rule.network.target =
      2 ^ n + decoratedLeafWeight (1 : ℕ) 0 n decorated := by
  induction n generalizing decorated with
  | zero =>
      rw [allocatedExpression]
      cases value : decorated []
      · simpa [value, decoratedLeafWeight, WheatstoneExpression.rule] using singleEdgeRule_distance
      · rw [if_pos rfl]
        change (wheatstoneRule singleEdgeRule singleEdgeRule singleEdgeRule).network.fullGraph.dist
          (wheatstoneRule singleEdgeRule singleEdgeRule singleEdgeRule).network.source
          (wheatstoneRule singleEdgeRule singleEdgeRule singleEdgeRule).network.target = _
        rw [wheatstoneRule_distance _ _ _ (singleEdgeRule_terminalProperties.connected _)
          (singleEdgeRule_terminalProperties.connected _) (singleEdgeRule_terminalProperties.connected _),
          singleEdgeRule_distance]
        norm_num [decoratedLeafWeight, value]
  | succ n induction_hypothesis =>
      rw [allocatedExpression]
      change (wheatstoneRule _ _ _).network.fullGraph.dist
        (wheatstoneRule _ _ _).network.source (wheatstoneRule _ _ _).network.target = _
      rw [wheatstoneRule_distance _ _ _
        ((allocatedExpression n (fun address => decorated (0 :: address))).terminalProperties.connected _)
        ((allocatedExpression n (fun address => decorated (1 :: address))).terminalProperties.connected _)
        ((allocatedExpression n (fun address => decorated (2 :: address))).terminalProperties.connected _)]
      rw [induction_hypothesis, induction_hypothesis, induction_hypothesis]
      have first := decoratedOuterLeaves_bound n (fun address => decorated (0 :: address))
      have second := decoratedOuterLeaves_bound n (fun address => decorated (1 :: address))
      simp only [decoratedLeafWeight, one_mul, zero_mul, add_zero, pow_succ]
      omega

theorem allocatedExpression_distance_bounds (n : ℕ) (decorated : List (Fin 3) → Bool) :
    2 ^ n ≤ (allocatedExpression n decorated).rule.network.fullGraph.dist
        (allocatedExpression n decorated).rule.network.source
        (allocatedExpression n decorated).rule.network.target ∧
      (allocatedExpression n decorated).rule.network.fullGraph.dist
        (allocatedExpression n decorated).rule.network.source
        (allocatedExpression n decorated).rule.network.target ≤ 2 ^ (n + 1) := by
  rw [allocatedExpression_distance]
  have bound := decoratedOuterLeaves_bound n decorated
  rw [pow_succ]
  omega

theorem allocatedExpression_classical (n : ℕ) (decorated : List (Fin 3) → Bool) (positive : 0 < n) :
    (allocatedExpression n decorated).rule.Classical := by
  apply WheatstoneExpression.classical
  cases n with
  | zero => omega
  | succ n => simp [allocatedExpression]

theorem decoratedOuterLeaves_eq_fibre (n : ℕ) (decorated : List (Fin 3) → Bool) :
    decoratedLeafWeight (1 : ℕ) 0 n decorated =
      ((projectedAddresses (List.replicate n false)).map
        (fun address => if decorated address then (1 : ℕ) else 0)).sum := by
  induction n generalizing decorated with
  | zero => simp [decoratedLeafWeight, projectedAddresses]
  | succ n induction_hypothesis =>
      simp only [decoratedLeafWeight, one_mul, zero_mul, add_zero,
        List.replicate_succ, projectedAddresses, List.map_append, List.map_map,
        Function.comp_def, List.sum_append, induction_hypothesis]

theorem allFalse_mem_binaryWords (n : ℕ) : List.replicate n false ∈ binaryWords n := by
  induction n with
  | zero => simp [binaryWords]
  | succ n induction_hypothesis =>
      rw [List.replicate_succ, binaryWords]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨_, induction_hypothesis, rfl⟩

theorem allocation_distance (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word) :
    (allocatedExpression n (allocationDecoration allocation)).rule.network.fullGraph.dist
      (allocatedExpression n (allocationDecoration allocation)).rule.network.source
      (allocatedExpression n (allocationDecoration allocation)).rule.network.target =
      2 ^ n + allocation (List.replicate n false) := by
  rw [allocatedExpression_distance, decoratedOuterLeaves_eq_fibre]
  have count := allocationDecoration_projected_sum allocation (List.replicate n false)
    (capacity _ (allFalse_mem_binaryWords n)) (fun _ => (1 : ℕ))
  simpa using count

end
end Universality.Section5
