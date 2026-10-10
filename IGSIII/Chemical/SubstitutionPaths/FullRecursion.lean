import IGSIII.Chemical.SubstitutionPaths.Erasure

set_option autoImplicit false

/-!
# Chemical recursion with arbitrary noncrossing child components

At every absent coarse edge this construction allows an arbitrary actual
noncrossing configuration, including components attached to either terminal.
Thus the graph realizing the recursion need not delete the dangling parts.
The local noncrossing condition concerns actual child connectivity, not a
distance recursion or its proposed conclusion. No probability law on these
configurations is asserted.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def fullDescendantConfiguration (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges) :
    (depth : ℕ) → List (Sym2 (Fin rule.vertices)) → Configuration (recursiveRule rule depth).edges
  | 0, address => innovation address
  | depth + 1, address => substitutionConfigurationEquiv (fun edge =>
      if innovation address edge then fullDescendantConfiguration rule innovation noncrossing depth
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)])
      else noncrossing depth address edge)

noncomputable def fullDescendantChildren (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    Fin rule.edges → Configuration (recursiveRule rule depth).edges :=
  fun edge => if innovation address edge then
    fullDescendantConfiguration rule innovation noncrossing depth
      (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)])
    else noncrossing depth address edge

theorem split_coarse_configuration {outerEdges vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (retained : Configuration outerEdges)
    (live dead : Fin outerEdges → Configuration edges)
    (liveCrosses : ∀ edge, retained edge = true → network.crosses (live edge) = true)
    (deadDoesNotCross : ∀ edge, retained edge = false → network.crosses (dead edge) = false) :
    network.coarseConfiguration (fun edge => if retained edge then live edge else dead edge) =
      retained := by
  funext edge
  change network.crosses (if retained edge then live edge else dead edge) = retained edge
  cases retention : retained edge with
  | false => simp only [Bool.false_eq_true, if_false]
             exact deadDoesNotCross edge retention
  | true => simp only [if_true]
            exact liveCrosses edge retention

theorem fullDescendant_crosses (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (recursiveRule rule depth).network.crosses
      (fullDescendantConfiguration rule innovation noncrossing depth address) = true := by
  induction depth generalizing address with
  | zero => exact crossing address
  | succ depth inductionHypothesis =>
      change (rule.network.substitute (recursiveRule rule depth).network).crosses
        (substitutionConfigurationEquiv
          (fullDescendantChildren rule innovation noncrossing depth address)) = true
      rw [substitute_crosses]
      have coarse := split_coarse_configuration (recursiveRule rule depth).network
        (innovation address)
        (fun edge => fullDescendantConfiguration rule innovation noncrossing depth
          (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
        (noncrossing depth address)
        (fun edge _ => inductionHypothesis
          (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
        (doesNotCross depth address)
      rw [show (recursiveRule rule depth).network.coarseConfiguration
        (fullDescendantChildren rule innovation noncrossing depth address) = innovation address
        from coarse]
      exact crossing address

theorem fullDescendant_coarse_configuration (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (recursiveRule rule depth).network.coarseConfiguration
        (fullDescendantChildren rule innovation noncrossing depth address) = innovation address :=
  split_coarse_configuration (recursiveRule rule depth).network (innovation address)
    (fun edge => fullDescendantConfiguration rule innovation noncrossing depth
      (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
    (noncrossing depth address)
    (fun edge _ => fullDescendant_crosses rule innovation crossing noncrossing doesNotCross depth
      (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
    (doesNotCross depth address)

/-- The chemical recursion holds for full finite configurations with arbitrary
noncrossing cells, not only for the graph obtained by deleting those cells. -/
theorem fullDescendant_distance_eq_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (((recursiveRule rule depth).network.openGraph
        (fullDescendantConfiguration rule innovation noncrossing depth address)).dist
          (recursiveRule rule depth).network.source
          (recursiveRule rule depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule innovation crossing) address (depth + 1) := by
  induction depth generalizing address with
  | zero =>
      change ((rule.network.openGraph (innovation address)).dist
          rule.network.source rule.network.target : ℝ) =
        terminalDistance (innovationPathFamily rule innovation crossing) address (0 + 1)
      rw [terminalDistance_succ]
      simp only [terminalDistance_zero]
      exact (graphPathFamily_shortest_unit _ _ _
        ((rule.network.crosses_eq_true _).mp (crossing address))).symm
  | succ depth inductionHypothesis =>
      have coarse := fullDescendant_coarse_configuration rule innovation crossing
        noncrossing doesNotCross depth address
      have reachable : (rule.network.openGraph
          ((recursiveRule rule depth).network.coarseConfiguration
            (fullDescendantChildren rule innovation noncrossing depth address))).Reachable
          rule.network.source rule.network.target := by
        rw [coarse]
        exact (rule.network.crosses_eq_true _).mp (crossing address)
      have oneStep := substitute_terminal_distance_eq_shortest rule.network
        (recursiveRule rule depth).network (fullDescendantChildren rule innovation noncrossing depth address)
        simple reachable
      simp only [coarse] at oneStep
      change (((rule.network.substitute (recursiveRule rule depth).network).openGraph
          (substitutionConfigurationEquiv
            (fullDescendantChildren rule innovation noncrossing depth address))).dist
            (rule.network.substitute (recursiveRule rule depth).network).source
            (rule.network.substitute (recursiveRule rule depth).network).target : ℝ) = _
      rw [oneStep, terminalDistance_succ]
      change (innovationPathFamily rule innovation crossing address).shortest _ =
        (innovationPathFamily rule innovation crossing address).shortest _
      apply shortest_congr_used
      intro path membership bond edgeMembership
      obtain ⟨edge, retained, rfl⟩ := graphPathFamily_used_edge rule.network (innovation address)
        ((rule.network.crosses_eq_true _).mp (crossing address)) membership edgeMembership
      rw [childDistanceCost_endpoint rule.network (recursiveRule rule depth).network
        (fullDescendantChildren rule innovation noncrossing depth address) simple edge]
      simp only [fullDescendantChildren, retained, if_true]
      exact inductionHypothesis
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)])

end IGSIII.Chemical.Substitution
