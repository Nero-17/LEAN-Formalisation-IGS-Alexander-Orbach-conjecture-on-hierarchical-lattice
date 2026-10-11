import Universality.Section5.WheatstoneThermal

namespace Universality.Section5
noncomputable section
open FiniteNetwork

def singleEdgeNetwork : FiniteNetwork 2 1 where
  endpoint _ := (0, 1)
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless _ := by decide

def singleEdgeRule : Rule := ⟨2, 1, singleEdgeNetwork⟩

theorem singleEdgeNetwork_crosses :
    ∀ configuration : Configuration 1, singleEdgeNetwork.crosses configuration = configuration 0 := by
  decide

theorem singleEdgeNetwork_reliability (p : ℝ) : singleEdgeNetwork.reliability p = p := by
  have configurations : (Finset.univ : Finset (Configuration 1)) = {![false], ![true]} := by decide
  simp [reliability, configurations, singleEdgeNetwork_crosses, bernoulliWeight, Fin.prod_univ_succ]

theorem singleEdgeNetwork_fairMassMatrix : singleEdgeNetwork.fairMassMatrix = 1 := by
  have counts : ∀ σ τ, singleEdgeNetwork.conditionalCount σ τ = if σ = τ then 1 else 0 := by decide
  have denominators : ∀ σ, singleEdgeNetwork.conditioningCount σ = 1 := by decide
  ext σ τ
  simp [fairMassMatrix, counts, denominators, Matrix.one_apply]

theorem singleEdgeNetwork_massMatrix : singleEdgeNetwork.massMatrix (1 / 2) = 1 := by
  ext σ τ
  rw [massMatrix_half, singleEdgeNetwork_fairMassMatrix]
  change ((1 : Matrix LiveState LiveState ℚ) σ τ : ℝ) = (1 : Matrix LiveState LiveState ℝ) σ τ
  by_cases equal : σ = τ <;> simp [Matrix.one_apply, equal]

theorem singleEdgeNetwork_derivative : deriv singleEdgeNetwork.reliability (1 / 2) = 1 := by
  have identity : singleEdgeNetwork.reliability = id := by
    funext p
    exact singleEdgeNetwork_reliability p
  rw [identity, deriv_id]

/-- A finite expression specifies a single fixed finite rule. -/
inductive WheatstoneExpression where
  | edge
  | node (a b c : WheatstoneExpression)

def WheatstoneExpression.rule : WheatstoneExpression → Rule
  | .edge => singleEdgeRule
  | .node a b c => wheatstoneRule a.rule b.rule c.rule

theorem WheatstoneExpression.fixed_half (expression : WheatstoneExpression) :
    expression.rule.network.reliability (1 / 2) = 1 / 2 := by
  induction expression with
  | edge => exact singleEdgeNetwork_reliability (1 / 2)
  | node a b c fixedA fixedB fixedC =>
      exact wheatstoneRule_fixed_half a.rule b.rule c.rule fixedA fixedB fixedC

theorem WheatstoneExpression.node_edges (a b c : WheatstoneExpression) :
    (WheatstoneExpression.node a b c).rule.edges =
      2 * a.rule.edges + 2 * b.rule.edges + c.rule.edges :=
  wheatstoneRule_edges a.rule b.rule c.rule

theorem WheatstoneExpression.node_derivative (a b c : WheatstoneExpression) :
    deriv (WheatstoneExpression.node a b c).rule.network.reliability (1 / 2) =
      3 / 4 * deriv a.rule.network.reliability (1 / 2) +
      3 / 4 * deriv b.rule.network.reliability (1 / 2) +
      1 / 8 * deriv c.rule.network.reliability (1 / 2) :=
  wheatstoneRule_derivative_half a.rule b.rule c.rule a.fixed_half b.fixed_half c.fixed_half

/-- The complete depth-n ternary allocation, with a Boolean decoration at each leaf. -/
def allocatedExpression : ℕ → (List (Fin 3) → Bool) → WheatstoneExpression
  | 0, decorated => if decorated [] then .node .edge .edge .edge else .edge
  | n + 1, decorated => .node
      (allocatedExpression n (fun address => decorated (0 :: address)))
      (allocatedExpression n (fun address => decorated (1 :: address)))
      (allocatedExpression n (fun address => decorated (2 :: address)))

theorem allocatedExpression_fixed_half (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).rule.network.reliability (1 / 2) = 1 / 2 :=
  (allocatedExpression n decorated).fixed_half

end
end Universality.Section5
