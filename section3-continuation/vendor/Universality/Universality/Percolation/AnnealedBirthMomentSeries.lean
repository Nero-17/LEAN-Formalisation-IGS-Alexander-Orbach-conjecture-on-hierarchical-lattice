import Universality.Percolation.RootedLimitSizeLaw
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Universality.Rule
noncomputable section
open scoped ENNReal

/-- The finite-cluster moment of the limiting actual uniform-root size law.
Extended nonnegative reals retain divergence instead of using a real `tsum`
whose value would be zero for a nonsummable series. -/
def limitingRootSizeMoment (rule : Rule) (p : ℝ) (order : ℕ) : ℝ≥0∞ :=
  ∑' size : ℕ, (size : ℝ≥0∞) ^ order *
    ENNReal.ofReal (rule.limitingRootSizeProbability p size)

/-- Actual birth counts weighted by cluster mass to a prescribed power. -/
def extendedBirthMoment (rule : Rule) (p : ℝ) (order generation : ℕ) : ℝ≥0∞ :=
  ∑' size : ℕ, (size : ℝ≥0∞) ^ order *
    ENNReal.ofReal (rule.expectedClusterBirth p size generation)

theorem limitingRootSizeMoment_birth_series (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    rule.limitingRootSizeMoment p order =
      ENNReal.ofReal (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ∑' generation : ℕ, ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
          rule.extendedBirthMoment p (order + 1) generation := by
  have hscale : 0 ≤ ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) := by
    have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
    have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
    exact div_nonneg (sub_nonneg.mpr hm.le) (sub_nonneg.mpr hv.le)
  have hseries (size : ℕ) : ENNReal.ofReal (rule.clusterSizeBirthSeries p size) =
      ∑' generation : ℕ, ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
        ENNReal.ofReal (rule.expectedClusterBirth p size generation) := by
    rw [clusterSizeBirthSeries, ENNReal.ofReal_tsum_of_nonneg]
    · apply tsum_congr
      intro generation
      exact ENNReal.ofReal_mul (by positivity)
    · intro generation
      exact mul_nonneg (by positivity) (rule.expectedClusterBirth_bounds hp hp' size generation).1
    · exact rule.clusterSizeBirthSeries_summable hedges hp hp' size
  unfold limitingRootSizeMoment limitingRootSizeProbability
  simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul hscale,
    ENNReal.ofReal_natCast, hseries, ← ENNReal.tsum_mul_left]
  calc
    _ = ∑' size : ℕ, ∑' generation : ℕ,
        ENNReal.ofReal (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
          (ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
            ((size : ℝ≥0∞) ^ (order + 1) *
              ENNReal.ofReal (rule.expectedClusterBirth p size generation))) := by
      apply tsum_congr
      intro size
      apply tsum_congr
      intro generation
      simp only [pow_succ]
      ac_rfl
    _ = _ := by
      rw [ENNReal.tsum_comm]
      simp only [extendedBirthMoment, ENNReal.tsum_mul_left]

end
end Universality.Rule
