import Universality.Percolation.Wheatstone

/-!
# Slot kernels of the Wheatstone operation

All kernels below are recomputed from the actual five-edge graph and its 32
configurations.  The opposite outer pair includes two edges; its multiplicity
must not be inserted again in the mass recursion.
-/

namespace Universality
open FiniteNetwork

def wheatstoneSlotCount (slots : Finset (Fin 5)) (σ τ : LiveState) : ℕ :=
  ∑ ω : Configuration 5,
    if wheatstoneNetwork.conditioning σ ω then
      (slots.filter fun e => wheatstoneNetwork.childState σ ω e = some τ).card
    else 0

def outerPairKernelCount : LiveState → LiveState → ℕ
  | .connected, .connected => 22
  | .connected, .both => 8
  | .connected, .single => 2
  | .both, .connected => 10
  | .both, .both => 14
  | .both, .single => 8
  | .single, .connected => 5
  | .single, .both => 1
  | .single, .single => 16

def centralKernelCount : LiveState → LiveState → ℕ
  | .connected, .connected => 9
  | .connected, .both => 5
  | .connected, .single => 2
  | .both, .connected => 6
  | .both, .both => 4
  | .both, .single => 4
  | .single, .connected => 3
  | .single, .both => 1
  | .single, .single => 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem wheatstone_outer_pair_counts :
    (∀ σ τ, wheatstoneSlotCount {0, 3} σ τ = outerPairKernelCount σ τ) ∧
    (∀ σ τ, wheatstoneSlotCount {1, 2} σ τ = outerPairKernelCount σ τ) := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem wheatstone_central_counts :
    ∀ σ τ, wheatstoneSlotCount {4} σ τ = centralKernelCount σ τ := by
  decide

def outerPairKernel : Matrix LiveState LiveState ℚ :=
  fun σ τ => (outerPairKernelCount σ τ : ℚ) / 16

def centralKernel : Matrix LiveState LiveState ℚ :=
  fun σ τ => (centralKernelCount σ τ : ℚ) / 16

theorem wheatstone_fair_mass_decomposition :
    wheatstoneNetwork.fairMassMatrix = (2 : ℚ) • outerPairKernel + centralKernel := by
  ext σ τ
  cases σ <;> cases τ <;>
    norm_num [wheatstone_fair_mass, wheatstoneCountTable, outerPairKernel,
      centralKernel, outerPairKernelCount, centralKernelCount]

end Universality
