import IGSIII.Mass.OrientedSpectralGap
import Universality.Percolation.RefinementPopulationVariance

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix
open scoped BigOperators

def OrientedState.massValue (values : MassLiveState → ℝ) : OrientedState → ℝ
  | .connected => values .connected
  | .both => values .both
  | .sourceOnly => values .sourceOnly
  | .targetOnly => values .targetOnly
  | .inactive => 0

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- A weighted count of the actual four live labels; inactive edges contribute zero. -/
noncomputable def orientedResponse (network : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges)
    (values : MassLiveState → ℝ) : ℝ :=
  ∑ edge, (network.orientedChildState sourceSelected targetSelected configuration edge).massValue values

theorem orientedResponse_eq (network : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges)
    (values : MassLiveState → ℝ) :
    network.orientedResponse sourceSelected targetSelected configuration values =
      ∑ child, network.orientedLiveCount sourceSelected targetSelected configuration child.oriented * values child := by
  simp only [orientedResponse, orientedLiveCount, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  cases network.orientedChildState sourceSelected targetSelected configuration edge <;>
    simp [sum_massLiveState, OrientedState.massValue, MassLiveState.oriented]

theorem orientedResponse_inactive (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (values : MassLiveState → ℝ) :
    network.orientedResponse false false configuration values = 0 := by
  simp [orientedResponse, inactive_has_no_live_children, OrientedState.massValue]

theorem orientedResponse_abs_le (network : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges)
    (values : MassLiveState → ℝ) :
    |network.orientedResponse sourceSelected targetSelected configuration values| ≤
      edges * ∑ child, |values child| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _edge : Fin edges, ∑ child : MassLiveState, |values child| := by
      apply Finset.sum_le_sum
      intro edge _
      cases network.orientedChildState sourceSelected targetSelected configuration edge <;>
        simp only [OrientedState.massValue, sum_massLiveState, abs_zero] <;>
        linarith [abs_nonneg (values .connected), abs_nonneg (values .both),
          abs_nonneg (values .sourceOnly), abs_nonneg (values .targetOnly)]
    _ = _ := by simp

theorem orientedResponse_connected (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (values : MassLiveState → ℝ) :
    network.orientedResponse true true configuration values =
      network.orientedResponse true false configuration values := by
  unfold orientedResponse orientedChildState
  simp_rw [network.selectedActive_connected configuration crossing]

theorem orientedMassMatrix_mulVec_response (network : FiniteNetwork vertices edges)
    (p : ℝ) (parent : MassLiveState) (values : MassLiveState → ℝ) :
    (network.orientedMassMatrix p *ᵥ values) parent =
      ∑ configuration, network.conditionalCellWeight p (parent.erase == .connected) configuration *
        network.orientedResponse parent.sourceSelected parent.targetSelected configuration values := by
  simp only [Matrix.mulVec, dotProduct, orientedMassMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [network.orientedResponse_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro child _
  ring

/-- Conditional offspring means retain both one-arm orientations. The connected
mask is simplified only on the support of the crossing-conditioned law. -/
theorem orientedResponse_conditional_mean (network : FiniteNetwork vertices edges)
    (p : ℝ) (parent : OrientedState) (opened : Bool) (values : MassLiveState → ℝ)
    (crossing : parent ≠ .inactive → (parent = .connected ↔ opened = true)) :
    (∑ configuration, network.conditionalCellWeight p opened configuration *
      network.orientedResponse parent.sourceSelected parent.targetSelected configuration values) =
      parent.massValue (network.orientedMassMatrix p *ᵥ values) := by
  cases parent with
  | inactive => simp [OrientedState.sourceSelected, OrientedState.targetSelected,
      network.orientedResponse_inactive, OrientedState.massValue]
  | connected =>
    have opened_true : opened = true := (crossing (by decide)).mp rfl
    rw [opened_true]
    change _ = (network.orientedMassMatrix p *ᵥ values) .connected
    rw [network.orientedMassMatrix_mulVec_response]
    apply Finset.sum_congr rfl
    intro configuration _
    simp only [OrientedState.sourceSelected, OrientedState.targetSelected,
      MassLiveState.sourceSelected, MassLiveState.targetSelected, MassLiveState.erase,
      show (LiveState.connected == LiveState.connected) = true from rfl]
    by_cases crosses : network.crosses configuration = true
    · rw [network.orientedResponse_connected configuration crosses]
    · simp [conditionalCellWeight, crosses]
  | both =>
    have opened_false : opened = false := Bool.eq_false_iff.mpr (fun opened_true =>
      OrientedState.noConfusion ((crossing (by decide)).mpr opened_true))
    rw [opened_false]
    exact (network.orientedMassMatrix_mulVec_response p .both values).symm
  | sourceOnly =>
    have opened_false : opened = false := Bool.eq_false_iff.mpr (fun opened_true =>
      OrientedState.noConfusion ((crossing (by decide)).mpr opened_true))
    rw [opened_false]
    exact (network.orientedMassMatrix_mulVec_response p .sourceOnly values).symm
  | targetOnly =>
    have opened_false : opened = false := Bool.eq_false_iff.mpr (fun opened_true =>
      OrientedState.noConfusion ((crossing (by decide)).mpr opened_true))
    rw [opened_false]
    exact (network.orientedMassMatrix_mulVec_response p .targetOnly values).symm

theorem orientedResponse_substitute (outer : FiniteNetwork outerVertices outerEdges)
    (inner : FiniteNetwork innerVertices innerEdges) (sourceSelected targetSelected : Bool)
    (cells : Fin outerEdges → Configuration innerEdges) (values : MassLiveState → ℝ) :
    (outer.substitute inner).orientedResponse sourceSelected targetSelected
      (substitutionConfigurationEquiv cells) values =
      ∑ edge, inner.orientedResponse
        (outer.orientedChildState sourceSelected targetSelected (inner.coarseConfiguration cells) edge).sourceSelected
        (outer.orientedChildState sourceSelected targetSelected (inner.coarseConfiguration cells) edge).targetSelected
        (cells edge) values := by
  unfold orientedResponse
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  apply Finset.sum_congr rfl
  intro child _
  rw [outer.orientedChildState_substitute]

end Universality.FiniteNetwork
