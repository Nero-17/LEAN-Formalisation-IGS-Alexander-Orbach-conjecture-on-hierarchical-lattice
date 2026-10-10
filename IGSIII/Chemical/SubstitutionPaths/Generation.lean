import IGSIII.Chemical.SubstitutionPaths.FullRecursion
import Universality.Graph.GenerationReassociation
import Universality.Graph.ClassicalRule

set_option autoImplicit false

/-!
# Identification with the existing IGS II generations

The explicit network equivalences in IGS II identify the top-down construction
with its existing bottom-up generation. Edge configurations are transported by
the same equivalence, so this is a statement about that actual finite graph.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def recursiveRuleEquivalence (rule : Rule) : (depth : ℕ) →
    (recursiveRule rule depth).network.NetworkEquivalence (rule.generation depth).network
  | 0 => NetworkEquivalence.refl rule.network
  | depth + 1 =>
      ((NetworkEquivalence.refl rule.network).substitute
        (recursiveRuleEquivalence rule depth)).trans
          (rule.generationTopDecomposition depth).symm

theorem networkEquivalence_terminal_distance
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges}
    {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (configuration : Configuration firstEdges)
    (reachable : (first.openGraph configuration).Reachable first.source first.target) :
    (second.openGraph (equivalence.configuration configuration)).dist second.source second.target =
      (first.openGraph configuration).dist first.source first.target := by
  have identity := iso_distance_eq (equivalence.openGraphIso configuration) reachable
  change (second.openGraph (equivalence.configuration configuration)).dist
      (equivalence.vertex first.source) (equivalence.vertex first.target) = _ at identity
  simpa only [equivalence.source, equivalence.target] using identity

noncomputable def fullGenerationConfiguration (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    Configuration (rule.generation depth).edges :=
  (recursiveRuleEquivalence rule depth).configuration
    (fullDescendantConfiguration rule innovation noncrossing depth address)

/-- The full deterministic chemical identity on the established IGS II graph
generations, including arbitrary noncrossing child components. -/
theorem generation_distance_eq_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (((rule.generation depth).network.openGraph
        (fullGenerationConfiguration rule innovation noncrossing depth address)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule innovation crossing) address (depth + 1) := by
  have reachable := ((recursiveRule rule depth).network.crosses_eq_true _).mp
    (fullDescendant_crosses rule innovation crossing noncrossing doesNotCross depth address)
  have identity := networkEquivalence_terminal_distance (recursiveRuleEquivalence rule depth)
    (fullDescendantConfiguration rule innovation noncrossing depth address) reachable
  change (((rule.generation depth).network.openGraph
      ((recursiveRuleEquivalence rule depth).configuration
        (fullDescendantConfiguration rule innovation noncrossing depth address))).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) = _
  rw [identity]
  exact fullDescendant_distance_eq_terminalDistance rule simple innovation crossing
    noncrossing doesNotCross depth address

/-- IGS II's classical-rule hypothesis supplies the exact simplicity assumption
used by the graph-to-recursion bridge. -/
theorem classical_generation_distance_eq_terminalDistance (rule : Rule) (classical : rule.Classical)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (((rule.generation depth).network.openGraph
        (fullGenerationConfiguration rule innovation noncrossing depth address)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule innovation crossing) address (depth + 1) :=
  generation_distance_eq_terminalDistance rule classical.simple innovation crossing
    noncrossing doesNotCross depth address

end IGSIII.Chemical.Substitution
