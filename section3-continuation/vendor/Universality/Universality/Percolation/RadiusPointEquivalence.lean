import Universality.Percolation.RadiusPointCounts

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

theorem internalRadiusPointRootCount (equivalence : R.NetworkEquivalence S)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Configuration eR) (radius : ℕ) :
    S.internalRadiusPointRootCount (equivalence.configuration configuration) radius =
      R.internalRadiusPointRootCount configuration radius := by
  have hfirst := equivalence.internalRadiusRootCount hconnected configuration radius
  have hsecond := equivalence.internalRadiusRootCount hconnected configuration (radius + 1)
  rw [S.internalRadiusRootCount_eq_point_add _ radius, R.internalRadiusRootCount_eq_point_add _ radius] at hfirst
  omega

theorem expectedInternalRadiusPointRootCount (equivalence : R.NetworkEquivalence S)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex) (p : ℝ) (radius : ℕ) :
    S.expectedInternalRadiusPointRootCount p radius = R.expectedInternalRadiusPointRootCount p radius := by
  simp only [FiniteNetwork.expectedInternalRadiusPointRootCount_eq_difference,
    equivalence.expectedInternalRadiusRootCount hconnected]

end
end Universality.FiniteNetwork.NetworkEquivalence
