import Universality.Percolation.AnnealedFiniteBirthMoments
import Universality.Percolation.ConditionalWeightComparison

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Each actual finite birth level is a polynomial expectation in the
Bernoulli parameter, hence continuous without any criticality assumption. -/
theorem continuous_expectedClusterBirthPower (rule : Rule) (order generation : ℕ) :
    Continuous (fun p : ℝ => rule.expectedClusterBirthPower p order generation) := by
  have hweight {edges : ℕ} (configuration : Configuration edges) :
      Continuous (fun p : ℝ => bernoulliWeight p configuration) :=
    continuous_iff_continuousAt.mpr (fun p => (differentiableAt_bernoulliWeight configuration p).continuousAt)
  cases generation with
  | zero =>
    unfold expectedClusterBirthPower expectedInternalClusterPower
    apply continuous_finset_sum
    intro configuration _
    exact (hweight configuration).mul continuous_const
  | succ generation =>
    unfold expectedClusterBirthPower expectedBirthClusterPower
    apply continuous_finset_sum
    intro configuration _
    exact (hweight configuration).mul continuous_const

/-- Real-valued form of the actual root-moment birth series, whenever its
already-defined extended moment is finite. -/
theorem limitingRootSizeMoment_toReal_birth_series (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ)
    (hfinite : rule.limitingRootSizeMoment p order ≠ ⊤) :
    (rule.limitingRootSizeMoment p order).toReal =
      (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ∑' generation : ℕ, (1 / (rule.edges : ℝ)) ^ (generation + 1) *
          rule.expectedClusterBirthPower p (order + 1) generation := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hs := (rule.limitingRootSizeMoment_finite_iff_birth_summable hedges hvertices hp hp' order).mp hfinite
  have hnonneg (generation : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ (generation + 1) *
      rule.expectedClusterBirthPower p (order + 1) generation :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr (zero_le_one.trans hm.le)) _)
      (rule.expectedClusterBirthPower_nonneg hp hp' _ _)
  rw [rule.limitingRootSizeMoment_expected_birth_series hedges hvertices hp hp' order]
  have hterm (generation : ℕ) :
      ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
        ENNReal.ofReal (rule.expectedClusterBirthPower p (order + 1) generation) =
      ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1) *
        rule.expectedClusterBirthPower p (order + 1) generation) :=
    (ENNReal.ofReal_mul (pow_nonneg (one_div_nonneg.mpr (zero_le_one.trans hm.le)) _)).symm
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hm.le) (sub_nonneg.mpr hv.le)),
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

end
end Universality.Rule
