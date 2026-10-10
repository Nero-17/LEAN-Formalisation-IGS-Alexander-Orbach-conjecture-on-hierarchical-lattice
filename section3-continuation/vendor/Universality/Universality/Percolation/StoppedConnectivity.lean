import Universality.Percolation.ConfigurationEncoding
import Universality.Graph.StoppedIteration

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def stoppedBitBall (ω : Configuration edges) (root : Fin vertices) (n : ℕ) : BitVec vertices :=
  iterateUntilFixed (R.maskExpand ω) n (vertexMask root)

theorem stoppedBitBall_eq (ω : Configuration edges) (root : Fin vertices) (n : ℕ) :
    R.stoppedBitBall ω root n = R.bitBall ω root n := by
  unfold stoppedBitBall
  rw [iterateUntilFixed_eq]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', bitBall, ih]

def stoppedIndexedConditioningCount (σ : LiveState) : ℕ :=
  ∑ index : Fin (2 ^ edges),
    let ω := decodeConfiguration (BitVec.ofFin index)
    let crossing := (R.stoppedBitBall ω R.source vertices).getLsbD R.target.val
    if (match σ with | .connected => crossing | .both | .single => !crossing)
    then 1 else 0

theorem stoppedIndexedConditioningCount_eq (σ : LiveState) :
    R.stoppedIndexedConditioningCount σ = R.conditioningCount σ := by
  rw [← indexedConditioningCount_eq]
  simp only [stoppedIndexedConditioningCount, indexedConditioningCount, bitReachable,
    stoppedBitBall_eq]
  rfl

end Universality.FiniteNetwork
