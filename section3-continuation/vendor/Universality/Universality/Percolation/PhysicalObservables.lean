import Universality.Graph.UniformRootSizeIdentification
import Universality.Percolation.AnnealedBirthMomentSeries
import Universality.Percolation.RootMassMonotonicity

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable (rule : Rule) [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

def physicalInfiniteClusterProbability (hedges : 1 < rule.edges) (p : ℝ) : ℝ :=
  if hp : 0 ≤ p ∧ p ≤ 1 then (rule.uniformRootSampleLaw hedges ⟨p, hp⟩).real
    {sample | rule.uniformRootInfiniteClusterEvent sample} else 0

def physicalFiniteClusterProbability (hedges : 1 < rule.edges) (p : ℝ) (size : ℕ) : ℝ :=
  if hp : 0 ≤ p ∧ p ≤ 1 then rule.uniformRootFiniteClusterProbability hedges ⟨p, hp⟩ size else 0

def physicalFiniteClusterMoment (hedges : 1 < rule.edges) (p : ℝ) (order : ℕ) : ℝ≥0∞ :=
  ∑' size : ℕ, (size : ℝ≥0∞) ^ order * ENNReal.ofReal (rule.physicalFiniteClusterProbability hedges p size)

theorem physicalInfiniteClusterProbability_eq (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    rule.physicalInfiniteClusterProbability hedges p = rule.escapingRootMass p := by
  unfold physicalInfiniteClusterProbability
  rw [dif_pos ⟨hp, hp'⟩]
  exact rule.uniformRootInfiniteClusterProbability_eq_escapingRootMass hedges hvertices ⟨p, hp, hp'⟩

theorem physicalFiniteClusterProbability_eq (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    rule.physicalFiniteClusterProbability hedges p size = rule.limitingRootSizeProbability p size := by
  unfold physicalFiniteClusterProbability
  rw [dif_pos ⟨hp, hp'⟩]
  exact rule.uniformRootFiniteClusterProbability_eq_limiting hedges hvertices ⟨p, hp, hp'⟩ size

theorem physicalFiniteClusterMoment_eq (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    rule.physicalFiniteClusterMoment hedges p order = rule.limitingRootSizeMoment p order := by
  unfold physicalFiniteClusterMoment limitingRootSizeMoment
  simp only [rule.physicalFiniteClusterProbability_eq hedges hvertices hp hp']

theorem Classical.physical_infinite_cluster_positive_iff (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 < rule.physicalInfiniteClusterProbability h.edges_gt_one p ↔ critical < p := by
  rw [rule.physicalInfiniteClusterProbability_eq h.edges_gt_one h.vertices_gt_two hp hp']
  exact h.escapingRootMass_pos_iff critical p hc hc' hfixed hp hp'

end
end Universality.Rule
