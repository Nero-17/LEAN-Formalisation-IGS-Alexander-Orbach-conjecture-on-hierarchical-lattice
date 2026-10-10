import IGSIII.Mass.JointMasks
import Universality.Percolation.OrientedStates

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

/-- The actual count of each oriented child, with the parent terminal mask
read from the same configuration. Inactive edges are also available for
exact finite identities, but are excluded from live populations. -/
noncomputable def orientedLiveCount (network : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges)
    (child : OrientedState) : ℝ :=
  ∑ edge, if network.orientedChildState sourceSelected targetSelected configuration edge = child then 1 else 0

/-- Erasing one-arm orientation merges precisely the two one-arm counts;
it does not identify their individual random coordinates. -/
theorem liveCount_oriented_split (network : FiniteNetwork vertices edges)
    (state : LiveState) (configuration : Configuration edges) :
    (network.liveCount state .connected configuration : ℝ) =
      network.orientedLiveCount true (state == .both) configuration .connected ∧
    (network.liveCount state .both configuration : ℝ) =
      network.orientedLiveCount true (state == .both) configuration .both ∧
    (network.liveCount state .single configuration : ℝ) =
      network.orientedLiveCount true (state == .both) configuration .sourceOnly +
      network.orientedLiveCount true (state == .both) configuration .targetOnly := by
  have count_eq (child : LiveState) :
      (network.liveCount state child configuration : ℝ) =
        ∑ edge, if (network.orientedChildState true (state == .both) configuration edge).eraseOrientation =
          some child then 1 else 0 := by
    simp only [liveCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro edge _
    rw [eraseOrientation_orientedChildState]
  constructor
  · rw [count_eq]
    unfold orientedLiveCount
    apply Finset.sum_congr rfl
    intro edge _
    cases network.orientedChildState true (state == .both) configuration edge <;>
      simp [OrientedState.eraseOrientation]
  constructor
  · rw [count_eq]
    unfold orientedLiveCount
    apply Finset.sum_congr rfl
    intro edge _
    cases network.orientedChildState true (state == .both) configuration edge <;>
      simp [OrientedState.eraseOrientation]
  · rw [count_eq]
    unfold orientedLiveCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    cases network.orientedChildState true (state == .both) configuration edge <;>
      simp [OrientedState.eraseOrientation]

theorem liveResponse_oriented_split (network : FiniteNetwork vertices edges)
    (state : LiveState) (configuration : Configuration edges) (values : LiveState → ℝ) :
    network.liveResponse state configuration values =
      network.orientedLiveCount true (state == .both) configuration .connected * values .connected +
      network.orientedLiveCount true (state == .both) configuration .both * values .both +
      (network.orientedLiveCount true (state == .both) configuration .sourceOnly +
        network.orientedLiveCount true (state == .both) configuration .targetOnly) * values .single := by
  obtain ⟨connected, both, single⟩ := network.liveCount_oriented_split state configuration
  rw [network.liveResponse_eq, sum_liveState, connected, both, single]

end Universality.FiniteNetwork
