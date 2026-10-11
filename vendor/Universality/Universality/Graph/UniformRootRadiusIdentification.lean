import Universality.Graph.AncestralRadiusEvents
import Universality.Graph.UniformRootEventIdentification
import Universality.Percolation.RadiusBirthSeries

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def generationRadiusTailEvent (rule : Rule) (radius depth : ℕ)
    (root : Fin (rule.generation depth).vertices)
    (configuration : FiniteNetwork.Configuration (rule.generation depth).edges) : Prop :=
  radius ≤ (rule.generation depth).network.rootClusterRadius configuration root

def uniformRootRadiusTailProbability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) (radius : ℕ) : ℝ :=
  (rule.uniformRootSampleLaw hedges p).real {sample | rule.uniformRootRadiusTailEvent radius sample}

theorem uniformVertexEventProbability_radiusTail (rule : Rule) (radius : ℕ) (p : ℝ) (depth : ℕ) :
    rule.uniformVertexEventProbability (rule.generationRadiusTailEvent radius) p depth =
      (rule.generation depth).network.uniformVertexRadiusTailProbability p radius := by
  unfold uniformVertexEventProbability generationRadiusTailEvent
    FiniteNetwork.uniformVertexRadiusTailProbability
  congr 1
  apply Finset.sum_congr rfl
  intro configuration _
  congr 1
  apply Finset.sum_congr rfl
  intro root _
  split_ifs <;> rfl

/-- The original finite uniform-root radius tails converge to the genuine
ambient-distance radius event of the independently constructed infinite graph. -/
theorem Classical.uniformVertexRadiusTailProbability_tendsto_sampleLaw {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (radius : ℕ) :
    Tendsto (fun depth =>
      (rule.generation depth).network.uniformVertexRadiusTailProbability (p : ℝ) radius)
      atTop (𝓝 (rule.uniformRootRadiusTailProbability h.edges_gt_one p radius)) := by
  have hlimit := rule.uniformVertexEventProbability_tendsto_of_ae_stabilize
    (rule.generationRadiusTailEvent radius) h.edges_gt_one h.vertices_gt_two p
    {sample | rule.uniformRootRadiusTailEvent radius sample}
    (h.measurableSet_uniformRootRadiusTailEvent radius) (by
      intro age
      exact Eventually.of_forall (fun sample =>
        h.ancestral_radiusTailEvent_stabilizes age radius sample))
  have hfunctions : rule.uniformVertexEventProbability (rule.generationRadiusTailEvent radius) (p : ℝ) =
      (fun depth => (rule.generation depth).network.uniformVertexRadiusTailProbability (p : ℝ) radius) :=
    funext (fun depth => rule.uniformVertexEventProbability_radiusTail radius p depth)
  rw [hfunctions] at hlimit
  exact hlimit

/-- At the nontrivial critical fixed point, the previously computed birth
series is exactly the physical infinite-graph radius tail. No off-critical
identification with that birth series is claimed. -/
theorem Classical.uniformRootRadiusTailProbability_eq_limiting {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) (radius : ℕ) :
    rule.uniformRootRadiusTailProbability h.edges_gt_one p radius =
      rule.limitingRootRadiusTailProbability (p : ℝ) radius :=
  tendsto_nhds_unique (h.uniformVertexRadiusTailProbability_tendsto_sampleLaw p radius)
    (h.uniformVertexRadiusTailProbability_tendsto p hp hp' hfixed radius)

end
end Universality.Rule
