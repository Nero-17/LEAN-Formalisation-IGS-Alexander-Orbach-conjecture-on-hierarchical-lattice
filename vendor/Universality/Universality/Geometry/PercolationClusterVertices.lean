import Universality.Geometry.GenerationMetricCells
import Universality.Percolation.InfiniteObservables

namespace Universality.Rule
noncomputable section
open FiniteNetwork MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Actual source-cluster vertices in the rescaled ambient completion. -/
def percolationClusterVertices {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) (depth : ℕ) :
    Set (GenerationMetricSpace h) :=
  generationMetricVertex h depth ''
    {vertex | ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source vertex}

theorem percolationClusterVertices_nonempty {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) (depth : ℕ) :
    (percolationClusterVertices h configuration depth).Nonempty :=
  ⟨_, _, SimpleGraph.Reachable.refl _, rfl⟩

theorem percolationClusterVertices_finite {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) (depth : ℕ) :
    (percolationClusterVertices h configuration depth).Finite :=
  (Set.toFinite _).image _

theorem generation_reachable_old_iff (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (first second : Fin (rule.generation depth).vertices) :
    ((rule.generation (depth + 1)).network.openGraph configuration).Reachable
      (rule.generationOldVertex depth first) (rule.generationOldVertex depth second) ↔
    ((rule.generation depth).network.openGraph (rule.coarsenGeneration depth configuration)).Reachable
      first second := by
  let cells := substitutionConfigurationEquiv.symm configuration
  have hequal : substitutionConfigurationEquiv cells = configuration :=
    substitutionConfigurationEquiv.apply_symm_apply configuration
  rw [← hequal]
  change (((rule.generation depth).network.substitute rule.network).openGraph
    (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin _ (Sum.inl first)) (Fintype.equivFin _ (Sum.inl second)) ↔ _
  simpa only [coarsenGeneration, Equiv.symm_apply_apply] using
    (((rule.generation depth).network.substitute_reachable_iff rule.network cells
    (Sum.inl first) (Sum.inl second)).trans
      ((rule.generation depth).network.substitutedReachable_iff rule.network cells first second))

theorem percolationClusterVertices_monotone {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n) :
    Monotone (percolationClusterVertices h configuration) := by
  apply monotone_nat_of_le_succ
  intro depth point hpoint
  obtain ⟨vertex, hvertex, rfl⟩ := hpoint
  refine ⟨rule.generationOldVertex depth vertex, ?_, (generationMetricVertex_old h depth vertex).symm⟩
  change ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
    (rule.generationOldVertex depth (rule.generation depth).network.source)
    (rule.generationOldVertex depth vertex)
  apply (generation_reachable_old_iff rule depth _ _ _).mpr
  simpa only [hcoarsen depth, Set.mem_setOf_eq] using hvertex

/-- No geometric-realisation premise: this is the closure of actual cluster vertices. -/
def percolationClusterLimit {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) : Set (GenerationMetricSpace h) :=
  closure (⋃ depth, percolationClusterVertices h configuration depth)

theorem percolationClusterLimit_compact {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) :
    IsCompact (percolationClusterLimit h configuration) := isClosed_closure.isCompact

theorem percolationClusterLimit_nonempty {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) :
    (percolationClusterLimit h configuration).Nonempty := by
  obtain ⟨point, hpoint⟩ := percolationClusterVertices_nonempty h configuration 0
  exact ⟨point, subset_closure (Set.mem_iUnion.mpr ⟨0, hpoint⟩)⟩

theorem infiniteLaw_clusterVertices_monotone {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true,
      Monotone (percolationClusterVertices h
        (fun n => ConfigurationHistory.latest rule n (path n))) := by
  filter_upwards [ConfigurationHistory.infiniteLaw_coarsens rule p hp hp' hfixed true]
    with path hpath
  exact percolationClusterVertices_monotone h _ hpath

end
end Universality.Rule
