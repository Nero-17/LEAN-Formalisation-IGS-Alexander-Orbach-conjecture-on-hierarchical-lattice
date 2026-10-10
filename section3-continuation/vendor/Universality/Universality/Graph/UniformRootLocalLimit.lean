import Universality.Graph.FullBallShapeEvents
import Universality.Graph.UniformRootEventIdentification
namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
attribute [local instance] Classical.propDecidable

def uniformVertexFullBallShapeProbability (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) (depth : ℕ) : ℝ :=
  (∑ root : Fin (rule.generation depth).vertices,
    if (rule.generation depth).network.ambientBallShape (fun _ => true) root radius
      targetGraph targetRoot then (1 : ℝ) else 0) / (rule.generation depth).vertices

theorem uniformVertexEventProbability_fullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) (p : ℝ) (depth : ℕ) :
    rule.uniformVertexEventProbability (rule.generationFullBallShape radius targetGraph targetRoot) p depth =
      rule.uniformVertexFullBallShapeProbability radius targetGraph targetRoot depth := by
  unfold uniformVertexEventProbability generationFullBallShape uniformVertexFullBallShapeProbability
  rw [← Finset.sum_mul, FiniteNetwork.sum_bernoulliWeight, one_mul]

/-- The constructed actual graph law is the uniformly rooted local limit:
every fixed-radius full-graph rooted-ball isomorphism event has the correct
finite-volume probability limit. -/
theorem Classical.uniformVertexFullBallShapeEventProbability_tendsto {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    Tendsto (rule.uniformVertexEventProbability
      (rule.generationFullBallShape radius targetGraph targetRoot) (p : ℝ)) atTop
      (𝓝 ((rule.uniformRootSampleLaw h.edges_gt_one p).real
        {sample | rule.uniformRootFullBallShape radius targetGraph targetRoot sample})) := by
  have hlimit := rule.uniformVertexEventProbability_tendsto_of_ae_stabilize
    (rule.generationFullBallShape radius targetGraph targetRoot)
    h.edges_gt_one h.vertices_gt_two p
    {sample | rule.uniformRootEventualFullBallShape radius targetGraph targetRoot sample}
    (rule.measurableSet_uniformRootEventualFullBallShape radius targetGraph targetRoot) (by
      intro age
      filter_upwards [h.ae_ancestral_fullBallShape_stabilizes p age radius targetGraph targetRoot]
        with sample hsample
      have heventual := eventualPredicate_iff_of_eventually_iff _ _ hsample
      filter_upwards [hsample] with n hn
      exact hn.trans heventual.symm)
  have hevents : {sample | rule.uniformRootEventualFullBallShape radius targetGraph targetRoot sample}
      =ᵐ[rule.uniformRootSampleLaw h.edges_gt_one p]
      {sample | rule.uniformRootFullBallShape radius targetGraph targetRoot sample} := by
    filter_upwards [h.ae_uniformRoot_eventualFullBallShape_iff p radius targetGraph targetRoot]
      with sample hsample
    exact propext hsample
  have hprobability : (rule.uniformRootSampleLaw h.edges_gt_one p).real
      {sample | rule.uniformRootEventualFullBallShape radius targetGraph targetRoot sample} =
      (rule.uniformRootSampleLaw h.edges_gt_one p).real
      {sample | rule.uniformRootFullBallShape radius targetGraph targetRoot sample} :=
    congrArg ENNReal.toReal (measure_congr hevents)
  rw [hprobability] at hlimit
  exact hlimit

/-- The unweighted uniform-vertex cylinder probabilities converge to the
actual infinite rooted graph, for every fixed radius and target rooted graph. -/
theorem Classical.uniformVertexFullBallShapeProbability_tendsto {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    Tendsto (rule.uniformVertexFullBallShapeProbability radius targetGraph targetRoot) atTop
      (𝓝 ((rule.uniformRootSampleLaw h.edges_gt_one p).real
        {sample | rule.uniformRootFullBallShape radius targetGraph targetRoot sample})) := by
  have hlimit := h.uniformVertexFullBallShapeEventProbability_tendsto p radius targetGraph targetRoot
  have hfunctions : rule.uniformVertexEventProbability
      (rule.generationFullBallShape radius targetGraph targetRoot) (p : ℝ) =
      rule.uniformVertexFullBallShapeProbability radius targetGraph targetRoot :=
    funext (fun depth => rule.uniformVertexEventProbability_fullBallShape radius targetGraph targetRoot p depth)
  rwa [hfunctions] at hlimit

end
end Universality.Rule
