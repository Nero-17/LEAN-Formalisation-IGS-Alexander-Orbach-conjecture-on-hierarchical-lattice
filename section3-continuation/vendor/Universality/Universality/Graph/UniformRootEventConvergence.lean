import Universality.Graph.FiniteAgeEventBounds
import Mathlib.Analysis.Normed.Group.Tannery

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable (rule : Rule) [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
variable (event : ∀ depth, Fin (rule.generation depth).vertices →
  FiniteNetwork.Configuration (rule.generation depth).edges → Prop)

theorem ageRootEventContribution_tendsto
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (age : ℕ) (p : unitInterval) (limitProbability : ℝ)
    (hlimit : Tendsto (fun n => (rule.ancestralSampleLaw age p).real
      (rule.ancestralStageEvent event age n)) atTop (𝓝 limitProbability)) :
    Tendsto (fun depth => rule.ageRootEventNumerator event depth age (p : ℝ) /
        (rule.generation depth).vertices) atTop
      (𝓝 ((((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1)) * limitProbability)) := by
  apply (tendsto_add_atTop_iff_nat age).mp
  have hweight : Tendsto (fun depth => rule.finiteRootAgeProbability (depth + age) age) atTop
      (𝓝 (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1))) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (rule.finiteRootAgeProbability_tendsto hedges hvertices age).comp (tendsto_add_atTop_nat age)
  convert hweight.mul hlimit using 1
  funext depth
  simpa only [Nat.add_comm] using
    (rule.weightedAncestralStageEventProbability event age depth p).symm

/-- Any convergent finite-stage event on every actual age-conditioned sample
space gives the finite uniform-root limit. The domination is proved from the
actual age counts; no exchange of an uncontrolled sum and limit is assumed. -/
theorem uniformVertexEventProbability_tendsto_mixture
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : unitInterval) (limitProbability : ℕ → ℝ)
    (hlimit : ∀ age, Tendsto (fun n => (rule.ancestralSampleLaw age p).real
      (rule.ancestralStageEvent event age n)) atTop (𝓝 (limitProbability age))) :
    Tendsto (rule.uniformVertexEventProbability event (p : ℝ)) atTop
      (𝓝 (∑' age, (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1)) *
        limitProbability age)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hgeom : Summable (fun age : ℕ => (1 / (rule.edges : ℝ)) ^ age) :=
    summable_geometric_of_lt_one (by positivity)
      ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
  have hsum := tendsto_tsum_of_dominated_convergence hgeom
    (fun age => rule.ageRootEventContribution_tendsto event hedges hvertices age p
      (limitProbability age) (hlimit age))
    (Eventually.of_forall (fun depth age => by
      have hbounds := rule.ageRootEventContribution_bounds event hedges depth age p
      rw [Real.norm_eq_abs, abs_of_nonneg hbounds.1]
      exact hbounds.2))
  have hfull := (rule.terminalRootEventContribution_tendsto_zero event hedges hvertices p).add hsum
  simp only [zero_add] at hfull
  convert hfull using 1
  funext depth
  have hfinite : (∑' age, rule.ageRootEventNumerator event depth age (p : ℝ) /
      (rule.generation depth).vertices) =
      ∑ age ∈ Finset.range (depth + 1), rule.ageRootEventNumerator event depth age (p : ℝ) /
        (rule.generation depth).vertices := by
    apply tsum_eq_sum
    intro age hage
    rw [rule.ageRootEventNumerator_eq_zero_of_lt event depth age
      (by have hle : depth + 1 ≤ age := by simpa only [Finset.mem_range, not_lt] using hage
          omega), zero_div]
  rw [hfinite]
  exact rule.uniformVertexEventProbability_by_age event depth (p : ℝ)

end
end Universality.Rule
