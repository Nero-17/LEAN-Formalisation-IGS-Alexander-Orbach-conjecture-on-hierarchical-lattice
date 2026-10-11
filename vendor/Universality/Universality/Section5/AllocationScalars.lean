import Universality.Section5.WheatstoneGrammar

set_option backward.isDefEq.respectTransparency false

namespace Universality.Section5
noncomputable section

/-- Weighted sum of decorated leaves, retaining the three distinct symbolic slots. -/
def decoratedLeafWeight {R : Type*} [Semiring R] (outer central : R) :
    ℕ → (List (Fin 3) → Bool) → R
  | 0, decorated => if decorated [] then 1 else 0
  | n + 1, decorated =>
      outer * decoratedLeafWeight outer central n (fun address => decorated (0 :: address)) +
      outer * decoratedLeafWeight outer central n (fun address => decorated (1 :: address)) +
      central * decoratedLeafWeight outer central n (fun address => decorated (2 :: address))

def ternaryAddresses : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (ternaryAddresses n).map (0 :: ·) ++
      (ternaryAddresses n).map (1 :: ·) ++ (ternaryAddresses n).map (2 :: ·)

def addressWeight {R : Type*} [Monoid R] (outer central : R) : List (Fin 3) → R
  | [] => 1
  | letter :: address => (if letter = 2 then central else outer) * addressWeight outer central address

theorem decoratedLeafWeight_eq_sum {R : Type*} [Semiring R] (outer central : R)
    (n : ℕ) (decorated : List (Fin 3) → Bool) :
    decoratedLeafWeight outer central n decorated =
      ((ternaryAddresses n).map (fun address =>
        if decorated address then addressWeight outer central address else 0)).sum := by
  induction n generalizing decorated with
  | zero => simp [decoratedLeafWeight, ternaryAddresses, addressWeight]
  | succ n induction_hypothesis =>
      simp only [decoratedLeafWeight, ternaryAddresses, List.map_append, List.map_map,
        List.sum_append, Function.comp_def, addressWeight]
      simp only [show (0 : Fin 3) ≠ 2 from by decide,
        show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte]
      have factor (coefficient value : R) (bit : Bool) :
          (if bit then coefficient * value else 0) = coefficient * (if bit then value else 0) := by
        cases bit <;> simp
      simp_rw [factor]
      simp only [List.sum_map_mul_left, ← induction_hypothesis]

theorem allocatedExpression_edges (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).rule.edges =
      5 ^ n + 4 * decoratedLeafWeight (2 : ℕ) 1 n decorated := by
  induction n generalizing decorated with
  | zero =>
      cases value : decorated [] <;>
        simp [allocatedExpression, value, decoratedLeafWeight,
          WheatstoneExpression.rule, wheatstoneRule_edges, singleEdgeRule]
  | succ n induction_hypothesis =>
      simp only [allocatedExpression, WheatstoneExpression.node_edges,
        induction_hypothesis, decoratedLeafWeight]
      ring

theorem allocatedExpression_derivative (n : ℕ) (decorated : List (Fin 3) → Bool) :
    deriv (allocatedExpression n decorated).rule.network.reliability (1 / 2) =
      (13 / 8 : ℝ) ^ n + 5 / 8 * decoratedLeafWeight (3 / 4 : ℝ) (1 / 8) n decorated := by
  induction n generalizing decorated with
  | zero =>
      rw [allocatedExpression]
      cases value : decorated []
      · simpa [value, decoratedLeafWeight, WheatstoneExpression.rule,
          singleEdgeRule] using singleEdgeNetwork_derivative
      · rw [if_pos rfl]
        simp only [value, Bool.true_eq, ↓reduceIte,
          WheatstoneExpression.node_derivative, decoratedLeafWeight, pow_zero]
        change 3 / 4 * deriv singleEdgeNetwork.reliability (1 / 2) +
          3 / 4 * deriv singleEdgeNetwork.reliability (1 / 2) +
          1 / 8 * deriv singleEdgeNetwork.reliability (1 / 2) = _
        rw [singleEdgeNetwork_derivative]
        norm_num
  | succ n induction_hypothesis =>
      simp only [allocatedExpression, WheatstoneExpression.node_derivative,
        induction_hypothesis, decoratedLeafWeight]
      ring

end
end Universality.Section5
