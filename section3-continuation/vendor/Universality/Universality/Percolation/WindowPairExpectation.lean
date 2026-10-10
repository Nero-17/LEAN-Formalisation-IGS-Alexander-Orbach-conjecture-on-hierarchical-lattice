import Universality.Percolation.ExpectedWindowLower

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def expectedConnectedWindowPairCount (R : FiniteNetwork vertices edges)
    (p lower upper : ℝ) : ℝ :=
  ∑ configuration : Configuration edges, bernoulliWeight p configuration *
    (R.connectedDistanceWindowPairs configuration lower upper).card

theorem averagedWindowConnectivity_eq (R : FiniteNetwork vertices edges)
    (p lower upper : ℝ) :
    R.averagedWindowConnectivity p lower upper =
      R.expectedConnectedWindowPairCount p lower upper / (R.distanceWindowPairs lower upper).card := rfl

theorem distanceWindowPairs_card_le_vertices_sq (R : FiniteNetwork vertices edges)
    (lower upper : ℝ) : (R.distanceWindowPairs lower upper).card ≤ vertices ^ 2 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Finset.card_le_univ (R.distanceWindowPairs lower upper)

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem expectedConnectedWindowPairCount_le_boundary_second_moment
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (lower upper : ℝ)
    (hseparation : (diameter : ℝ) < lower) :
    (R.substitute S).expectedConnectedWindowPairCount p lower upper ≤
      (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) *
        ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * S.expectedInternalBoundaryMoment p 2) := by
  apply le_trans _ (R.expected_farConnectedPairs_le_boundary_second_moment S hinner
    diameter hdiameter hp hp')
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
  exact_mod_cast (R.substitute S).connectedDistanceWindowPairs_card_le_far
    configuration lower upper diameter hseparation

end
end Universality.FiniteNetwork
