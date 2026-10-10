import Universality.Graph.FiniteAgeBounds
import Universality.Graph.UniformRootProbabilitySpace
import Universality.Percolation.RootedLimitSizeLaw
import Mathlib.Analysis.Normed.Group.Tannery

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem ageRootClusterContribution_tendsto (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (age size : ℕ) (p : unitInterval) :
    Tendsto (fun depth => rule.ageRootClusterNumerator depth age (p : ℝ) size /
        (rule.generation depth).vertices) atTop
      (𝓝 ((((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1)) *
        rule.ancestralFiniteClusterProbability age size p)) := by
  apply (tendsto_add_atTop_iff_nat age).mp
  have hweight : Tendsto (fun depth => rule.finiteRootAgeProbability (depth + age) age) atTop
      (𝓝 (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1))) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (rule.finiteRootAgeProbability_tendsto hedges hvertices age).comp (tendsto_add_atTop_nat age)
  have hlimit := hweight.mul (rule.ancestralFiniteClusterProbability_tendsto age size p)
  convert hlimit using 1
  funext depth
  simpa only [Nat.add_comm] using
    (rule.weightedAncestralStageClusterProbability age depth size p).symm

/-- Actual finite uniform-root cluster probabilities converge to the finite
component events of the constructed random direct-limit graph. The proof
disintegrates by true vertex age and controls the age tail geometrically. -/
theorem generation_uniformRootSample_size_tendsto (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : unitInterval) (size : ℕ) :
    Tendsto (fun depth =>
      (rule.generation depth).network.uniformVertexClusterMassProbability (p : ℝ) size)
      atTop (𝓝 (rule.uniformRootFiniteClusterProbability hedges p size)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hgeom : Summable (fun age : ℕ => (1 / (rule.edges : ℝ)) ^ age) :=
    summable_geometric_of_lt_one (by positivity)
      ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
  have hsum := tendsto_tsum_of_dominated_convergence hgeom
    (fun age => rule.ageRootClusterContribution_tendsto hedges hvertices age size p)
    (Eventually.of_forall (fun depth age => by
      have hbounds := rule.ageRootClusterContribution_bounds hedges depth age size p
      rw [Real.norm_eq_abs, abs_of_nonneg hbounds.1]
      exact hbounds.2))
  rw [← rule.uniformRootFiniteClusterProbability_eq_mixture hedges p size] at hsum
  have hlimit := (rule.terminalRootClusterContribution_tendsto_zero hedges hvertices p size).add hsum
  simp only [zero_add] at hlimit
  convert hlimit using 1
  funext depth
  have hfinite : (∑' age, rule.ageRootClusterNumerator depth age (p : ℝ) size /
      (rule.generation depth).vertices) =
      ∑ age ∈ Finset.range (depth + 1), rule.ageRootClusterNumerator depth age (p : ℝ) size /
        (rule.generation depth).vertices := by
    apply tsum_eq_sum
    intro age hage
    rw [rule.ageRootClusterNumerator_eq_zero_of_lt depth age
      (by have hle : depth + 1 ≤ age := by simpa only [Finset.mem_range, not_lt] using hage
          omega), zero_div]
  rw [hfinite]
  exact rule.uniformVertexClusterProbability_by_age depth (p : ℝ) size

/-- Identification with the previously proved finite-volume limit uses
uniqueness of that limit, rather than defining the graph law to be it. -/
theorem uniformRootFiniteClusterProbability_eq_limiting (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : unitInterval) (size : ℕ) :
    rule.uniformRootFiniteClusterProbability hedges p size =
      rule.limitingRootSizeProbability (p : ℝ) size :=
  tendsto_nhds_unique (rule.generation_uniformRootSample_size_tendsto hedges hvertices p size)
    (rule.generation_uniformVertexClusterMassProbability_tendsto hedges hvertices p.property.1 p.property.2 size)

theorem uniformRootInfiniteClusterProbability_eq_escapingRootMass (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : unitInterval) :
    (rule.uniformRootSampleLaw hedges p).real
      {sample | rule.uniformRootInfiniteClusterEvent sample} = rule.escapingRootMass (p : ℝ) := by
  rw [rule.uniformRootInfiniteClusterProbability_eq]
  simp only [rule.uniformRootFiniteClusterProbability_eq_limiting hedges hvertices p]
  rfl

end
end Universality.Rule
