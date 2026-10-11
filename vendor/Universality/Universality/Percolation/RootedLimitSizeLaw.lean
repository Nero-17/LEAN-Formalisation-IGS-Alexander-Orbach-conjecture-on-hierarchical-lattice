import Universality.Percolation.CriticalSizeTotalVariation

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- The pointwise finite-volume limit of the actual uniformly sampled vertex's
cluster-size probabilities. This definition does not assert a rooted graph limit. -/
def limitingRootSizeProbability (rule : Rule) (p : ℝ) (size : ℕ) : ℝ :=
  (size : ℝ) * (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
    rule.clusterSizeBirthSeries p size)

theorem limitingRootSizeProbability_nonneg (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ rule.limitingRootSizeProbability p size := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (rule.generation_uniformVertexClusterMassProbability_tendsto hedges hvertices hp hp' size)
  exact Eventually.of_forall (fun n =>
    (rule.generation n).network.uniformVertexClusterMassProbability_nonneg hp hp' size)

theorem limitingRootSizeProbability_sum_le_one (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (sizes : Finset ℕ) :
    ∑ size ∈ sizes, rule.limitingRootSizeProbability p size ≤ 1 := by
  have hlimit : Tendsto (fun n : ℕ => ∑ size ∈ sizes,
      (rule.generation n).network.uniformVertexClusterMassProbability p size) atTop
      (𝓝 (∑ size ∈ sizes, rule.limitingRootSizeProbability p size)) :=
    tendsto_finsetSum sizes (fun size _ =>
      rule.generation_uniformVertexClusterMassProbability_tendsto hedges hvertices hp hp' size)
  apply le_of_tendsto hlimit
  apply Eventually.of_forall
  intro n
  have hsum := (rule.generation n).network.uniformVertexClusterMassProbability_hasSum p
  rw [← hsum.tsum_eq]
  exact hsum.summable.sum_le_tsum sizes (fun size _ =>
    (rule.generation n).network.uniformVertexClusterMassProbability_nonneg hp hp' size)

theorem limitingRootSizeProbability_summable (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Summable (rule.limitingRootSizeProbability p) := by
  exact summable_of_sum_le
    (fun size => rule.limitingRootSizeProbability_nonneg hedges hvertices hp hp' size)
    (rule.limitingRootSizeProbability_sum_le_one hedges hvertices hp hp')

theorem limitingRootSizeProbability_tsum_le_one (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ∑' size, rule.limitingRootSizeProbability p size ≤ 1 := by
  exact Real.tsum_le_of_sum_le
    (fun size => rule.limitingRootSizeProbability_nonneg hedges hvertices hp hp' size)
    (rule.limitingRootSizeProbability_sum_le_one hedges hvertices hp hp')

/-- Mass escaping every fixed finite-size cutoff, with volume sent to infinity
first. Identifying it with an infinite-cluster probability needs a rooted graph. -/
def escapingRootMass (rule : Rule) (p : ℝ) : ℝ :=
  1 - ∑' size, rule.limitingRootSizeProbability p size

theorem escapingRootMass_bounds (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ rule.escapingRootMass p ∧ rule.escapingRootMass p ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (rule.limitingRootSizeProbability_tsum_le_one hedges hvertices hp hp')
  · have hnonneg : 0 ≤ ∑' size, rule.limitingRootSizeProbability p size := tsum_nonneg (fun size =>
      rule.limitingRootSizeProbability_nonneg hedges hvertices hp hp' size)
    unfold escapingRootMass
    linarith

theorem root_size_cutoff_volume_limit (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (cutoff : ℕ) :
    Tendsto (fun n : ℕ => 1 - ∑ size ∈ Finset.range cutoff,
      (rule.generation n).network.uniformVertexClusterMassProbability p size) atTop
      (𝓝 (1 - ∑ size ∈ Finset.range cutoff, rule.limitingRootSizeProbability p size)) := by
  exact tendsto_const_nhds.sub (tendsto_finsetSum _ (fun size _ =>
    rule.generation_uniformVertexClusterMassProbability_tendsto hedges hvertices hp hp' size))

theorem root_size_cutoff_limit (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Tendsto (fun cutoff : ℕ => 1 - ∑ size ∈ Finset.range cutoff,
      rule.limitingRootSizeProbability p size) atTop (𝓝 (rule.escapingRootMass p)) := by
  exact tendsto_const_nhds.sub
    (rule.limitingRootSizeProbability_summable hedges hvertices hp hp').hasSum.tendsto_sum_nat

theorem Classical.critical_escapingRootMass_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    rule.escapingRootMass p = 0 := by
  unfold escapingRootMass limitingRootSizeProbability
  rw [(h.critical_cluster_size_mass_hasSum p hp hp' hfixed).tsum_eq, sub_self]

end
end Universality.Rule
