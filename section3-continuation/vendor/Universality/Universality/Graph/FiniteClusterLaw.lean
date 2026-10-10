import Universality.Graph.FiniteClusterIndicator
import Universality.Graph.StageProductLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def sampledStageClusterSize (tower : NetworkTower)
    (root : Fin (tower.stage 0).vertices) (n : ℕ)
    (bits : (Σ k, Fin (tower.stage k).edges) → Bool) : ℕ :=
  ((tower.stage n).network.clusterVertices
    (tower.restrictConfiguration (tower.sampledConfiguration bits) n)
    (tower.vertexMap 0 n (Nat.zero_le n) root)).card

theorem measurable_sampledStageClusterSize (tower : NetworkTower)
    (law : Measure Bool) [IsProbabilityMeasure law]
    (root : Fin (tower.stage 0).vertices) (n : ℕ) :
    Measurable (tower.sampledStageClusterSize root n) :=
  (measurable_of_countable (fun configuration => ((tower.stage n).network.clusterVertices
    configuration (tower.vertexMap 0 n (Nat.zero_le n) root)).card)).comp
      (tower.sampledConfiguration_restrict_measurePreserving law n).measurable

theorem measurableSet_sampledFiniteClusterSize (tower : NetworkTower)
    (law : Measure Bool) [IsProbabilityMeasure law]
    (root : Fin (tower.stage 0).vertices) (size : ℕ) :
    MeasurableSet {bits | tower.finiteClusterSizeEvent (tower.sampledConfiguration bits) root size} := by
  simp only [tower.finiteClusterSizeEvent_iff_eventually_card, Set.setOf_exists, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro first
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro h
  exact (tower.measurable_sampledStageClusterSize law root n) (measurableSet_singleton size)

/-- For the actual independently sampled direct-limit graph, the finite-cell
cluster probabilities converge to its genuine finite-component probability. -/
theorem sampledFiniteClusterSize_probability_tendsto (tower : NetworkTower)
    (law : Measure Bool) [IsProbabilityMeasure law]
    (root : Fin (tower.stage 0).vertices) (size : ℕ) :
    Tendsto (fun n => (tower.rawEdgeLaw law).real
      {bits | tower.sampledStageClusterSize root n bits = size}) atTop
      (𝓝 ((tower.rawEdgeLaw law).real
        {bits | tower.finiteClusterSizeEvent (tower.sampledConfiguration bits) root size})) := by
  classical
  have hstage (n : ℕ) : MeasurableSet {bits | tower.sampledStageClusterSize root n bits = size} :=
    (tower.measurable_sampledStageClusterSize law root n) (measurableSet_singleton size)
  have hlimit := tower.measurableSet_sampledFiniteClusterSize law root size
  have hintegral := tendsto_integral_of_dominated_convergence (μ := tower.rawEdgeLaw law)
    (fun _ => (1 : ℝ))
    (F := fun n => {bits | tower.sampledStageClusterSize root n bits = size}.indicator (fun _ => (1 : ℝ)))
    (f := {bits | tower.finiteClusterSizeEvent (tower.sampledConfiguration bits) root size}.indicator
      (fun _ => (1 : ℝ)))
    (fun n => (measurable_const.indicator (hstage n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun bits => by
      simp only [Set.indicator_apply]
      split <;> norm_num))
    (Eventually.of_forall (fun bits => by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, sampledStageClusterSize] using
        tower.finite_cluster_size_indicator_tendsto (tower.sampledConfiguration bits) root size))
  simpa only [integral_indicator_const (1 : ℝ) (hstage _),
    integral_indicator_const (1 : ℝ) hlimit, smul_eq_mul, mul_one] using hintegral

end
end Universality.NetworkTower
