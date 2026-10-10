import IGSIII.Mass.OrientedResponse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix
open scoped BigOperators

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem orientedResponse_erase (network : FiniteNetwork vertices edges)
    (state : LiveState) (configuration : Configuration edges) (values : LiveState → ℝ) :
    network.orientedResponse true (state == .both) configuration (fun child => values child.erase) =
      network.liveResponse state configuration values := by
  rw [network.orientedResponse_eq, sum_massLiveState, network.liveResponse_oriented_split]
  simp only [MassLiveState.oriented, MassLiveState.erase]
  ring

theorem orientedResponse_second_moment_le (network : FiniteNetwork vertices edges)
    (p : ℝ) (positive : 0 ≤ p) (below_one : p ≤ 1)
    (reliability_positive : 0 < network.reliability p)
    (reliability_below_one : network.reliability p < 1)
    (opened : Bool) (parent : OrientedState) (values : MassLiveState → ℝ) :
    (∑ configuration, network.conditionalCellWeight p opened configuration *
      network.orientedResponse parent.sourceSelected parent.targetSelected configuration values ^ 2) ≤
      parent.massValue (fun _ => (edges * ∑ child, |values child|) ^ 2) := by
  by_cases inactive : parent = .inactive
  · subst parent
    simp [OrientedState.sourceSelected, OrientedState.targetSelected,
      network.orientedResponse_inactive, OrientedState.massValue]
  have live_value : parent.massValue (fun _ => (edges * ∑ child, |values child|) ^ 2) =
      (edges * ∑ child, |values child|) ^ 2 := by
    cases parent <;> simp_all [OrientedState.massValue]
  rw [live_value]
  calc
    _ ≤ ∑ configuration, network.conditionalCellWeight p opened configuration *
        (edges * ∑ child, |values child|) ^ 2 := by
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (network.conditionalCellWeight_nonneg positive below_one _ _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (network.orientedResponse_abs_le parent.sourceSelected parent.targetSelected configuration values) 2
    _ = _ := by rw [← Finset.sum_mul,
      network.sum_conditionalCellWeight p reliability_positive reliability_below_one, one_mul]

/-- The actual four-type refinement innovation has at most a fixed second
moment per live coarse cell. All four labels are read from the same cells. -/
theorem refinement_orientedResponse_variance_le (outer : FiniteNetwork outerVertices outerEdges)
    (inner : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (positive : 0 ≤ p) (below_one : p ≤ 1)
    (reliability_positive : 0 < inner.reliability p)
    (reliability_below_one : inner.reliability p < 1)
    (coarse : Configuration outerEdges) (state : LiveState) (values : MassLiveState → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
      ((outer.substitute inner).orientedResponse true (state == .both)
        (substitutionConfigurationEquiv cells) values -
        outer.orientedResponse true (state == .both) coarse (inner.orientedMassMatrix p *ᵥ values)) ^ 2) ≤
      outer.liveResponse state coarse (fun _ => (innerEdges * ∑ child, |values child|) ^ 2) := by
  classical
  have mean : outer.orientedResponse true (state == .both) coarse (inner.orientedMassMatrix p *ᵥ values) =
      ∑ edge, ∑ configuration, inner.conditionalCellWeight p (coarse edge) configuration *
        inner.orientedResponse
          (outer.orientedChildState true (state == .both) coarse edge).sourceSelected
          (outer.orientedChildState true (state == .both) coarse edge).targetSelected configuration values := by
    unfold orientedResponse
    apply Finset.sum_congr rfl
    intro edge _
    exact (inner.orientedResponse_conditional_mean p _ (coarse edge) values
      (outer.live_oriented_state_determines_crossing true (state == .both) coarse edge)).symm
  have local_response (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
        ((outer.substitute inner).orientedResponse true (state == .both)
          (substitutionConfigurationEquiv cells) values -
          outer.orientedResponse true (state == .both) coarse (inner.orientedMassMatrix p *ᵥ values)) ^ 2 =
      (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
        ((∑ edge, inner.orientedResponse
          (outer.orientedChildState true (state == .both) coarse edge).sourceSelected
          (outer.orientedChildState true (state == .both) coarse edge).targetSelected (cells edge) values) -
          outer.orientedResponse true (state == .both) coarse (inner.orientedMassMatrix p *ᵥ values)) ^ 2 := by
    rw [← inner.coarse_fiber_conditional_joint_weight]
    by_cases compatible : inner.coarseConfiguration cells = coarse
    · rw [outer.orientedResponse_substitute, compatible]
    · simp [compatible]
  simp_rw [local_response]
  rw [mean]
  apply (finite_product_variance_le_second_moments
    (fun edge configuration => inner.conditionalCellWeight p (coarse edge) configuration)
    (fun edge configuration => inner.orientedResponse
      (outer.orientedChildState true (state == .both) coarse edge).sourceSelected
      (outer.orientedChildState true (state == .both) coarse edge).targetSelected configuration values)
    (fun edge => inner.sum_conditionalCellWeight p reliability_positive reliability_below_one (coarse edge))).trans
  rw [← outer.orientedResponse_erase]
  unfold orientedResponse
  exact Finset.sum_le_sum (fun edge _ => inner.orientedResponse_second_moment_le p positive below_one
    reliability_positive reliability_below_one (coarse edge) _ values)

end Universality.FiniteNetwork
