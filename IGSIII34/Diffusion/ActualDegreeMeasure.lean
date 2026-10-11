import IGSIII34.Diffusion.ActualFiniteWalk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry MeasureTheory

instance actualFiniteClusterDecidableEq (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    DecidableEq (ActualFiniteCluster rule configuration scale scalePositive depth) := Classical.decEq _

/-- The reversible degree probability measure on the same entire finite
cluster and the same chemical metric carrier used by Section 2. -/
def actualFiniteClusterDegreeMeasure (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    Measure (ActualFiniteCluster rule configuration scale scalePositive depth) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) (crossing depth)
  exact degreeMeasure (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))

instance actualFiniteClusterDegreeMeasure_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    IsProbabilityMeasure (actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth) := by
  unfold actualFiniteClusterDegreeMeasure degreeMeasure
  infer_instance

theorem actualFiniteClusterDegreeMeasure_singleton (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (vertex : ActualFiniteCluster rule configuration scale scalePositive depth) :
    actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth {vertex} =
      ENNReal.ofReal (degree (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)) vertex /
        (2 * (rule.generation depth).network.liveCount .connected .connected (configuration depth))) := by
  unfold actualFiniteClusterDegreeMeasure degreeMeasure
  rw [finiteWeightPMF_singleton]
  simp only [degreeWeight, clusterEdge_card]

end
end IGSIII34.Diffusion
