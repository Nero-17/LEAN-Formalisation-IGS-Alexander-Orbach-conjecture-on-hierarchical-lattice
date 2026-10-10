import Universality.Section5.WheatstoneMass
import Universality.Section5.AllocationRealisation
import Universality.Graph.Section5Classical

namespace Universality.Section5
noncomputable section
open FiniteNetwork Matrix

theorem WheatstoneExpression.massMatrix (expression : WheatstoneExpression) :
    expression.rule.network.massMatrix (1 / 2) = expression.matrixResponse K3real J3real := by
  induction expression with
  | edge => exact singleEdgeNetwork_massMatrix
  | node a b c first second central =>
      let involutions : (edge : Fin 5) →
          TerminalInvolution (![a.rule,b.rule,b.rule,a.rule,c.rule] edge) :=
        Fin.cases a.terminalProperties.involution
          (Fin.cases b.terminalProperties.involution
            (Fin.cases b.terminalProperties.involution
              (Fin.cases a.terminalProperties.involution
                (Fin.cases c.terminalProperties.involution (fun edge => Fin.elim0 edge)))))
      change (wheatstoneRule a.rule b.rule c.rule).network.massMatrix (1 / 2) =
        K3real * a.matrixResponse K3real J3real + K3real * b.matrixResponse K3real J3real +
          J3real * c.matrixResponse K3real J3real
      rw [wheatstoneRule_massMatrix a.rule b.rule c.rule a.fixed_half b.fixed_half c.fixed_half
        (fun edge => (involutions edge).symmetry) (fun edge => (involutions edge).source)
        (fun edge => (involutions edge).target), first, second, central]

theorem allocatedExpression_massMatrix (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).rule.network.massMatrix (1 / 2) =
      (2 * K3real + J3real) ^ n +
        ((ternaryAddresses n).map (fun address => if decorated address then
          addressWeight K3real J3real address * (2 * K3real + J3real - 1) else 0)).sum := by
  rw [WheatstoneExpression.massMatrix, allocatedExpression_matrixResponse_ordered_sum]

theorem allocation_massMatrix (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word) :
    (allocatedExpression n (allocationDecoration allocation)).rule.network.massMatrix (1 / 2) =
      (2 * K3real + J3real) ^ n +
        ((binaryWords n).map (fun word => allocation word • wordProduct K3real J3real word)).sum *
          (2 * K3real + J3real - 1) := by
  rw [WheatstoneExpression.massMatrix, allocatedExpression_matrixResponse,
    decoratedLeafWeight_from_allocation _ _ _ _ capacity]
  simp only [two_mul]

end
end Universality.Section5
