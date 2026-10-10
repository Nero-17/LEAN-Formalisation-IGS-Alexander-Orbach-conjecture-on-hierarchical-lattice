import Universality.Percolation.RadiusPointLaw

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ}

def clusterRadiusPointRootCount (R : FiniteNetwork vertices edges) (cluster : Finset (Fin vertices))
    (radius : ℕ) : ℕ := (cluster.filter fun root => R.clusterRadius cluster root = radius).card

def internalRadiusPointRootCount (R : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (radius : ℕ) : ℕ := ∑ cluster ∈ R.internalClusterFamily configuration,
      R.clusterRadiusPointRootCount cluster radius

def expectedInternalRadiusPointRootCount (R : FiniteNetwork vertices edges) (p : ℝ) (radius : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalRadiusPointRootCount configuration radius

theorem clusterRadiusRootCount_eq_point_add (R : FiniteNetwork vertices edges)
    (cluster : Finset (Fin vertices)) (radius : ℕ) :
    R.clusterRadiusRootCount cluster radius = R.clusterRadiusPointRootCount cluster radius +
      R.clusterRadiusRootCount cluster (radius + 1) := by
  classical
  simp only [clusterRadiusRootCount, clusterRadiusPointRootCount, Finset.card_eq_sum_ones,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro root _
  split_ifs <;> omega

theorem internalRadiusRootCount_eq_point_add (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (radius : ℕ) :
    R.internalRadiusRootCount configuration radius = R.internalRadiusPointRootCount configuration radius +
      R.internalRadiusRootCount configuration (radius + 1) := by
  unfold internalRadiusRootCount internalRadiusPointRootCount
  simp_rw [R.clusterRadiusRootCount_eq_point_add _ radius, Finset.sum_add_distrib]

theorem expectedInternalRadiusPointRootCount_eq_difference (R : FiniteNetwork vertices edges)
    (p : ℝ) (radius : ℕ) : R.expectedInternalRadiusPointRootCount p radius =
      R.expectedInternalRadiusRootCount p radius - R.expectedInternalRadiusRootCount p (radius + 1) := by
  have hh : R.expectedInternalRadiusRootCount p radius = R.expectedInternalRadiusPointRootCount p radius +
      R.expectedInternalRadiusRootCount p (radius + 1) := by
    unfold expectedInternalRadiusRootCount expectedInternalRadiusPointRootCount
    simp_rw [R.internalRadiusRootCount_eq_point_add _ radius, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  linarith

end
end Universality.FiniteNetwork
