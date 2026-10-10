import Universality.Geometry.PercolationRecursiveTree
import Universality.Percolation.InfiniteTerminalCondition

/-! The concrete interface for manuscript Theorem 2.9. All metric spaces,
cluster sets, cell maps, inherited types and probability laws are constructed
from the actual classical rule. There is no assumed geometric realisation. -/

namespace Universality.Rule
noncomputable section
open FiniteNetwork MeasureTheory Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def percolationHistoryProcess (rule : Rule) (path : Π n, rule.ConfigurationHistory n) :
    PercolationCellProcess rule where
  configuration n := ConfigurationHistory.latest rule n (path n)
  sourceSelected := true
  targetSelected := false

/-- The full conditional cell law factors into the prescribed rule-choice law.
This identity retains every configuration, not just its expected mass. -/
theorem percolationCell_conditional_joint_weight (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (depth : ℕ) (opened : Bool)
    (configuration : Configuration (rule.generation (depth + 1)).edges) :
    (rule.generation (depth + 1)).network.conditionalCellWeight p opened configuration =
      rule.network.conditionalCellWeight p opened
        ((rule.generation depth).network.coarseConfiguration
          (rule.percolationCellConfiguration depth configuration)) *
      ∏ edge : Fin rule.edges, (rule.generation depth).network.conditionalCellWeight p
        ((rule.generation depth).network.coarseConfiguration
          (rule.percolationCellConfiguration depth configuration) edge)
        (rule.percolationCellConfiguration depth configuration edge) := by
  have h := rule.network.conditional_substitution_joint_weight (rule.generation depth).network
    p hp hp' (rule.generation_fixed_point p hfixed depth) opened
    ((rule.generation depth).network.coarseConfiguration
      (rule.percolationCellConfiguration depth configuration))
    (rule.percolationCellConfiguration depth configuration)
  rw [if_pos rfl] at h
  rw [h]
  have hequal := (rule.generationTopDecomposition depth).conditionalCellWeight p opened configuration
  have hconfiguration : substitutionConfigurationEquiv
      (rule.percolationCellConfiguration depth configuration) =
      (rule.generationTopDecomposition depth).configuration configuration :=
    substitutionConfigurationEquiv.apply_symm_apply _
  rw [hconfiguration]
  exact hequal.symm

/-- Actual critical, terminal-connected percolation clusters converge almost surely
in GH space to the compact set satisfying the finite-type random recursive
equations at every address. The ambient metric is the rescaled graph metric. -/
theorem classical_percolation_graphDirected_gromovHausdorff {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true,
      (∀ n, (rule.generation n).network.crosses (ConfigurationHistory.latest rule n (path n)) = true) ∧
      Tendsto (fun n => (percolationClusterCompact h
        (fun k => ConfigurationHistory.latest rule k (path k)) n).toGHSpace) atTop
        (𝓝 (percolationLimitCompact h
          (fun k => ConfigurationHistory.latest rule k (path k))).toGHSpace) ∧
      (percolationHistoryProcess rule path).limit h =
        percolationClusterLimit h (fun n => ConfigurationHistory.latest rule n (path n)) ∧
      (∀ address : List (Fin rule.edges),
        IsCompact (((percolationHistoryProcess rule path).atAddress address).limit h) ∧
        ((percolationHistoryProcess rule path).atAddress address).limit h =
          ⋃ edge : Fin rule.edges, generationMetricCell h edge ''
            (((percolationHistoryProcess rule path).atAddress address).child edge).limit h) ∧
      (∀ n, ConfigurationHistory.recursiveLabels rule n (path n) =
        ConfigurationHistory.globalLabels rule n (path n)) := by
  filter_upwards [ConfigurationHistory.infiniteLaw_coarsens rule p hp hp' hfixed true,
    ConfigurationHistory.infiniteLaw_terminal_condition rule p hp hp' hfixed true,
    ConfigurationHistory.infiniteLaw_recursiveLabels rule p hp hp' hfixed true]
    with path hcoherent hconnected hlabels
  refine ⟨hconnected, percolationCluster_gromovHausdorff h _ hcoherent,
    percolationSelectedLimit_source h _, ?_, hlabels⟩
  intro address
  exact ⟨PercolationCellProcess.limit_compact _ h,
    (percolationHistoryProcess rule path).graphDirected_at_every_address h hcoherent address⟩

end
end Universality.Rule
