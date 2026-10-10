import Universality.Geometry.IncreasingCompactLimit
import Universality.Geometry.PercolationClusterVertices
import Mathlib.Topology.MetricSpace.GromovHausdorff

namespace Universality.Rule
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology

def percolationClusterCompact {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, FiniteNetwork.Configuration (rule.generation n).edges) (depth : ℕ) :
    NonemptyCompacts (GenerationMetricSpace h) where
  carrier := percolationClusterVertices h configuration depth
  isCompact' := (percolationClusterVertices_finite h configuration depth).isCompact
  nonempty' := percolationClusterVertices_nonempty h configuration depth

def percolationLimitCompact {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, FiniteNetwork.Configuration (rule.generation n).edges) :
    NonemptyCompacts (GenerationMetricSpace h) where
  carrier := percolationClusterLimit h configuration
  isCompact' := percolationClusterLimit_compact h configuration
  nonempty' := percolationClusterLimit_nonempty h configuration

/-- The actual ambient-metric clusters converge; no assumed geometric realisation occurs. -/
theorem percolationCluster_gromovHausdorff {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, FiniteNetwork.Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n) :
    Tendsto (fun n => (percolationClusterCompact h configuration n).toGHSpace) atTop
      (𝓝 (percolationLimitCompact h configuration).toGHSpace) := by
  apply GromovHausdorff.toGHSpace_continuous.continuousAt.tendsto.comp
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact Geometry.increasing_sets_hausdorff_tendsto _
    (percolationClusterVertices_monotone h configuration hcoarsen)
    (percolationClusterVertices_nonempty h configuration)
    (percolationClusterLimit_compact h configuration)

/-- Almost-sure Gromov--Hausdorff convergence under the genuine conditional recursive law. -/
theorem infiniteLaw_percolationCluster_gromovHausdorff {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true,
      Tendsto (fun n => (percolationClusterCompact h
        (fun k => ConfigurationHistory.latest rule k (path k)) n).toGHSpace) atTop
        (𝓝 (percolationLimitCompact h
          (fun k => ConfigurationHistory.latest rule k (path k))).toGHSpace) := by
  filter_upwards [ConfigurationHistory.infiniteLaw_coarsens rule p hp hp' hfixed true]
    with path hpath
  exact percolationCluster_gromovHausdorff h _ hpath

end
end Universality.Rule
