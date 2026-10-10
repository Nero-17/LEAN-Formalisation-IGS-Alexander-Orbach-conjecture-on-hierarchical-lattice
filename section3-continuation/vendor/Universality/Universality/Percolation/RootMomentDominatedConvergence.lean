import Universality.Percolation.RealAnnealedMoment
import Mathlib.Analysis.Normed.Group.Tannery

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 200000
attribute [local irreducible] expectedClusterBirthPower limitingRootSizeMoment

/-- Split off the finite initial generation before applying dominated convergence. -/
theorem limitingRootSizeMoment_toReal_shifted_birth_series (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ)
    (hs : Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 2) *
      rule.expectedClusterBirthPower p (order + 1) (n + 1))) :
    (rule.limitingRootSizeMoment p order).toReal =
      (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ((1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 +
          ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) *
            rule.expectedClusterBirthPower p (order + 1) (n + 1)) := by
  have hsfull : Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirthPower p (order + 1) n) :=
    (summable_nat_add_iff 1).mp hs
  have hfinite := (rule.limitingRootSizeMoment_finite_iff_birth_summable hedges hvertices hp hp' order).mpr hsfull
  calc
    _ = (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirthPower p (order + 1) n :=
      rule.limitingRootSizeMoment_toReal_birth_series hedges hvertices hp hp' order hfinite
    _ = _ := by
      apply congrArg (fun value : ℝ => (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) * value)
      simpa only [Nat.zero_add, pow_one, Nat.add_assoc, Nat.reduceAdd] using hsfull.tsum_eq_zero_add

/-- Tannery's theorem applied to the actual birth series. Only the genuine
shifted birth terms need domination; the initial finite level is continuous. -/
theorem root_moment_tendsto_of_birth_domination (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (critical : ℝ) (hc : 0 ≤ critical) (hc' : critical ≤ 1) (order : ℕ)
    (filter : Filter ℝ) (hfilter : Tendsto (fun p : ℝ => p) filter (𝓝 critical))
    (hinterior : ∀ᶠ p in filter, 0 ≤ p ∧ p ≤ 1)
    (bound : ℕ → ℝ) (hboundSum : Summable bound)
    (hbound : ∀ᶠ p in filter, ∀ n : ℕ,
      (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1) ≤ bound n)
    (hcritical : rule.limitingRootSizeMoment critical order ≠ ⊤) :
    Tendsto (fun p : ℝ => (rule.limitingRootSizeMoment p order).toReal) filter
      (𝓝 (rule.limitingRootSizeMoment critical order).toReal) := by
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (show 0 < rule.edges by omega)
  have hnonneg (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (n : ℕ) :
      0 ≤ (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1) :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hm.le) _) (rule.expectedClusterBirthPower_nonneg hp hp' _ _)
  have hsumLimit : Tendsto
      (fun p : ℝ => ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1))
      filter (𝓝 (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower critical (order + 1) (n + 1))) := by
    apply tendsto_tsum_of_dominated_convergence hboundSum
    · intro n
      exact ((continuous_const.mul (rule.continuous_expectedClusterBirthPower (order + 1) (n + 1))).tendsto critical).comp hfilter
    · filter_upwards [hinterior, hbound] with p hp hb
      intro n
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg p hp.1 hp.2 n)] using hb n
  have hcriticalSum := (rule.limitingRootSizeMoment_finite_iff_birth_summable hedges hvertices hc hc' order).mp hcritical
  have hinitialLimit : Tendsto
      (fun p : ℝ => (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0)
      filter (𝓝 ((1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower critical (order + 1) 0)) :=
    ((continuous_const.mul (rule.continuous_expectedClusterBirthPower (order + 1) 0)).tendsto critical).comp hfilter
  have hresult : Tendsto
      (fun p : ℝ => (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ((1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 +
          ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)))
      filter (𝓝 ((((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ((1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower critical (order + 1) 0 +
          ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower critical (order + 1) (n + 1)))) :=
    tendsto_const_nhds.mul (hinitialLimit.add hsumLimit)
  rw [rule.limitingRootSizeMoment_toReal_shifted_birth_series hedges hvertices critical hc hc' order
    ((summable_nat_add_iff 1).mpr hcriticalSum)]
  apply hresult.congr'
  filter_upwards [hinterior, hbound] with p hp hb
  exact (rule.limitingRootSizeMoment_toReal_shifted_birth_series hedges hvertices p hp.1 hp.2 order
    (hboundSum.of_nonneg_of_le (hnonneg p hp.1 hp.2) hb)).symm

end
end Universality.Rule
