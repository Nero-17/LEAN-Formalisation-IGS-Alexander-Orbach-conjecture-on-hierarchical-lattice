import IGSIII.Chemical.SubstitutionPaths.Bounds
import Universality.Percolation.InfiniteConfigurationLaw
import Universality.Percolation.ConditionalSubstitutionLaw

set_option autoImplicit false

/-!
# Extracting chemical data from actual configuration histories

The root and children below are obtained by the existing explicit network
reassociation, applied to the finest configuration in the actual history.
They are not supplied as a certificate. The weighted distance is zero on
disconnected pairs; the connected conditional law is treated explicitly.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem networkEquivalence_terminal_distance_all
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges}
    {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (configuration : Configuration firstEdges) :
    (second.openGraph (equivalence.configuration configuration)).dist second.source second.target =
      (first.openGraph configuration).dist first.source first.target := by
  by_cases reachable : (first.openGraph configuration).Reachable first.source first.target
  · exact networkEquivalence_terminal_distance equivalence configuration reachable
  · have secondUnreachable : ¬ (second.openGraph (equivalence.configuration configuration)).Reachable
        second.source second.target := by
      intro secondReachable
      have crossing := (second.crosses_eq_true _).mpr secondReachable
      rw [equivalence.crosses] at crossing
      exact reachable ((first.crosses_eq_true _).mp crossing)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable reachable,
      SimpleGraph.dist_eq_zero_of_not_reachable secondUnreachable]

noncomputable def cellMinPlus {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) : ℝ :=
  weightedDistance (outer.openGraph coarse)
    (fun bond => (childDistanceCost outer inner cells bond : ℝ)) outer.source outer.target

theorem substitute_distance_eq_cellMinPlus
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (cells : Fin outerEdges → Configuration innerEdges) :
    (((outer.substitute inner).openGraph (substitutionConfigurationEquiv cells)).dist
        (outer.substitute inner).source (outer.substitute inner).target : ℝ) =
      cellMinPlus outer inner (inner.coarseConfiguration cells) cells := by
  by_cases reachable : (outer.openGraph (inner.coarseConfiguration cells)).Reachable
      outer.source outer.target
  · rw [substitute_terminal_distance_eq_shortest outer inner cells simple reachable]
    exact (weightedDistance_of_reachable _ _ reachable).symm
  · have fineUnreachable : ¬ ((outer.substitute inner).openGraph
        (substitutionConfigurationEquiv cells)).Reachable
        (outer.substitute inner).source (outer.substitute inner).target := by
      intro fineReachable
      have crossing := ((outer.substitute inner).crosses_eq_true _).mpr fineReachable
      rw [substitute_crosses] at crossing
      exact reachable ((outer.crosses_eq_true _).mp crossing)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable fineUnreachable]
    simp [cellMinPlus, weightedDistance, reachable]

noncomputable def generationTopCellsEquiv (rule : Rule) (depth : ℕ) :
    Configuration (rule.generation (depth + 1)).edges ≃
      (Fin rule.edges → Configuration (rule.generation depth).edges) :=
  (rule.generationTopDecomposition depth).configuration.trans substitutionConfigurationEquiv.symm

noncomputable def generationTopCells (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges) :
    Fin rule.edges → Configuration (rule.generation depth).edges :=
  generationTopCellsEquiv rule depth fine

theorem configuration_of_topCells (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges) :
    substitutionConfigurationEquiv (generationTopCells rule depth fine) =
      (rule.generationTopDecomposition depth).configuration fine := by
  simp [generationTopCells, generationTopCellsEquiv]

noncomputable def generationRootConfiguration (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges) : Configuration rule.edges :=
  (rule.generation depth).network.coarseConfiguration (generationTopCells rule depth fine)

theorem generation_root_crosses (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges) :
    rule.network.crosses (generationRootConfiguration rule depth fine) =
      (rule.generation (depth + 1)).network.crosses fine := by
  have identity := (rule.generationTopDecomposition depth).crosses fine
  rw [← configuration_of_topCells rule depth fine, substitute_crosses] at identity
  exact identity

/-- Exact chemical identity derived from an arbitrary actual finest-level
configuration, with its root and children extracted canonically. -/
theorem generation_distance_eq_cellMinPlus (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (depth : ℕ) (fine : Configuration (rule.generation (depth + 1)).edges) :
    (((rule.generation (depth + 1)).network.openGraph fine).dist
        (rule.generation (depth + 1)).network.source
        (rule.generation (depth + 1)).network.target : ℝ) =
      cellMinPlus rule.network (rule.generation depth).network
        (generationRootConfiguration rule depth fine) (generationTopCells rule depth fine) := by
  have identity := networkEquivalence_terminal_distance_all (rule.generationTopDecomposition depth) fine
  rw [← identity, ← configuration_of_topCells rule depth fine]
  exact substitute_distance_eq_cellMinPlus rule.network (rule.generation depth).network simple _

noncomputable def historyRootConfiguration (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) : Configuration rule.edges :=
  generationRootConfiguration rule depth (Rule.ConfigurationHistory.latest rule (depth + 1) history)

noncomputable def historyChildConfiguration (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) :
    Fin rule.edges → Configuration (rule.generation depth).edges :=
  generationTopCells rule depth (Rule.ConfigurationHistory.latest rule (depth + 1) history)

theorem history_child_crossing (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) (edge : Fin rule.edges) :
    (rule.generation depth).network.crosses (historyChildConfiguration rule depth history edge) =
      historyRootConfiguration rule depth history edge := rfl

theorem history_distance_eq_cellMinPlus (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (depth : ℕ) (history : rule.ConfigurationHistory (depth + 1)) :
    (((rule.generation (depth + 1)).network.openGraph
        (Rule.ConfigurationHistory.latest rule (depth + 1) history)).dist
        (rule.generation (depth + 1)).network.source
        (rule.generation (depth + 1)).network.target : ℝ) =
      cellMinPlus rule.network (rule.generation depth).network
        (historyRootConfiguration rule depth history) (historyChildConfiguration rule depth history) :=
  generation_distance_eq_cellMinPlus rule simple depth _

theorem history_law_latest_crosses (rule : Rule) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ) :
    ∀ᵐ history ∂Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth,
      (rule.generation depth).network.crosses (Rule.ConfigurationHistory.latest rule depth history) =
        opened := by
  apply ae_iff_of_countable.mpr
  intro history positiveAtom
  by_contra notCrossing
  apply positiveAtom
  change (finiteWeightPMF _ _ _).toMeasure {history} = 0
  rw [finiteWeightPMF_singleton,
    Rule.ConfigurationHistory.recursiveWeight_eq_directWeight rule p positive lessOne fixedPoint]
  simp [Rule.ConfigurationHistory.directWeight, FiniteNetwork.conditionalCellWeight, notCrossing]

/-- All finite actual configurations have the prescribed crossing state on
the same existing IGS II probability space, simultaneously in depth. -/
theorem infinite_history_latest_crosses (rule : Rule) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ depth, (rule.generation depth).network.crosses
        (Rule.ConfigurationHistory.latest rule depth (path depth)) = opened := by
  apply ae_all_iff.mpr
  intro depth
  have crossing := history_law_latest_crosses rule p positive lessOne fixedPoint opened depth
  rw [← Rule.ConfigurationHistory.infiniteLaw_marginal rule p positive lessOne fixedPoint opened depth]
    at crossing
  exact ae_of_ae_map (measurable_pi_apply depth).aemeasurable crossing

end IGSIII.Chemical.Substitution
