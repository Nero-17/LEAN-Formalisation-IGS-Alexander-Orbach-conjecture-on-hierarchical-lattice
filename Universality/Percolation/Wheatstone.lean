import Universality.Percolation.FiniteNetwork
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Universality.Matrix.TwoByTwo

namespace Universality
open FiniteNetwork

/-- Vertex order: source, target, upper, lower. Edge order: source-upper,
upper-target, source-lower, lower-target, upper-lower. -/
def wheatstoneNetwork : FiniteNetwork 4 5 where
  endpoint := ![(0, 2), (2, 1), (0, 3), (3, 1), (2, 3)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wheatstone_conditioning_connected :
    wheatstoneNetwork.conditioningCount .connected = 16 := by
  decide

def wheatstoneCountTable : LiveState → LiveState → ℕ
  | .connected, .connected => 53
  | .connected, .both => 21
  | .connected, .single => 6
  | .both, .connected => 26
  | .both, .both => 32
  | .both, .single => 20
  | .single, .connected => 13
  | .single, .both => 3
  | .single, .single => 36

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wheatstone_exact_counts :
    (∀ σ, wheatstoneNetwork.conditioningCount σ = 16) ∧
      (∀ σ τ, wheatstoneNetwork.conditionalCount σ τ = wheatstoneCountTable σ τ) := by
  decide

theorem wheatstone_fair_mass (σ τ : LiveState) :
    wheatstoneNetwork.fairMassMatrix σ τ = (wheatstoneCountTable σ τ : ℚ) / 16 := by
  simp [fairMassMatrix, wheatstone_exact_counts.1, wheatstone_exact_counts.2]

/-- The two-dimensional block is extracted from actual conditional expectations
using the invariant plane `(a,2b,b)`, in the basis used by the paper. -/
def fairMassBlock {v e : ℕ} (R : FiniteNetwork v e) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![R.fairMassMatrix .connected .connected,
     2 * R.fairMassMatrix .connected .both + R.fairMassMatrix .connected .single;
     R.fairMassMatrix .single .connected,
     2 * R.fairMassMatrix .single .both + R.fairMassMatrix .single .single]

theorem wheatstone_fair_block : fairMassBlock wheatstoneNetwork = wheatstoneBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fairMassBlock, wheatstone_fair_mass, wheatstoneCountTable, wheatstoneBlock]

end Universality
