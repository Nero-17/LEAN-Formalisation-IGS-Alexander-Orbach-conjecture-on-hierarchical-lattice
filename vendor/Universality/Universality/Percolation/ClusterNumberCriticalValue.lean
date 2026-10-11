import Universality.Percolation.ClusterNumberSeries

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- At any fixed point, the actual density is determined by one-cell internal
cluster counting, without any differentiability assumption. -/
theorem clusterNumberSeries_fixed_point (hedges : 1 < edges)
    (p : Set.Icc (0 : ℝ) 1) (hfixed : R.reliability p.val = p.val) :
    R.clusterNumberSeries p =
      R.expectedInternalClusterNumber p.val / ((vertices : ℝ) - 2) := by
  have hunit : R.unitReliability p = p := Subtype.ext hfixed
  have hequation := R.clusterNumberSeries_equation hedges p
  rw [hunit] at hequation
  have hedgesreal : (1 : ℝ) < edges := by exact_mod_cast hedges
  have hne : (edges : ℝ) - 1 ≠ 0 := (sub_pos.mpr hedgesreal).ne'
  apply (mul_left_cancel₀ hne)
  calc
    ((edges : ℝ) - 1) * R.clusterNumberSeries p =
        ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) *
          R.expectedInternalClusterNumber p.val := by linarith
    _ = _ := by ring

end
end Universality.FiniteNetwork
