import IGSIII34.Resistance.IGSII
import IGSIII34.Resistance.Pivotal
import Universality.Percolation.ConditionalPivotal

/-!
# The genuine open-edge electrical network of a Bernoulli configuration

Closed edges are removed from the edge type, not assigned a finite artificial
resistance. The resulting graph and its one-edge deletions are identified with
the exact configuration graphs of IGS II.
-/

set_option autoImplicit false

namespace IGSIII34.Percolation
noncomputable section

open Resistance

def network {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges) :
    FiniteNetwork (Fin vertices) {edge : Fin edges // configuration edge = true} where
  endpoint edge := rule.endpoint edge.val
  source := rule.source
  target := rule.target
  distinct := rule.terminals_distinct

theorem graph_eq_openGraph {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges) :
    (network rule configuration).graph = rule.openGraph configuration := by
  ext first second
  constructor
  · rintro ⟨distinct, ⟨edge, opened⟩, orientation⟩
    exact ⟨distinct, edge, opened, orientation⟩
  · rintro ⟨distinct, edge, opened, orientation⟩
    exact ⟨distinct, ⟨edge, opened⟩, orientation⟩

theorem graphWithoutEdge_eq_updated_openGraph {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges)
    (removed : {edge : Fin edges // configuration edge = true}) :
    (network rule configuration).graphWithoutEdge removed =
      rule.openGraph (Function.update configuration removed.val false) := by
  ext first second
  constructor
  · rintro ⟨distinct, ⟨edge, opened⟩, retained, orientation⟩
    have different : edge ≠ removed.val := by
      intro equality
      exact retained (Subtype.ext equality)
    exact ⟨distinct, edge, by simpa only [Function.update_of_ne different] using opened, orientation⟩
  · rintro ⟨distinct, edge, opened, orientation⟩
    have different : edge ≠ removed.val := by
      intro equality
      subst edge
      simp at opened
    have originallyOpen : configuration edge = true := by
      simpa only [Function.update_of_ne different] using opened
    exact ⟨distinct, ⟨edge, originallyOpen⟩,
      (fun equality => different (congrArg Subtype.val equality)), orientation⟩

theorem connected_of_crosses {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges)
    (crosses : rule.crosses configuration = true) :
    (network rule configuration).graph.Reachable
      (network rule configuration).source (network rule configuration).target := by
  change (network rule configuration).graph.Reachable rule.source rule.target
  rw [graph_eq_openGraph]
  exact (rule.crosses_eq_true configuration).mp crosses

theorem pivotal_disconnects_open_network {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges)
    (removed : {edge : Fin edges // configuration edge = true})
    (pivotal : rule.pivotal configuration removed.val = true) :
    ¬ ((network rule configuration).graphWithoutEdge removed).Reachable
      rule.source rule.target := by
  rw [graphWithoutEdge_eq_updated_openGraph]
  have deletionClosed : rule.crosses (Function.update configuration removed.val false) = false := by
    have parts : rule.crosses (Function.update configuration removed.val true) = true ∧
        rule.crosses (Function.update configuration removed.val false) = false := by
      simpa only [Universality.FiniteNetwork.pivotal, Bool.and_eq_true, Bool.not_eq_true'] using pivotal
    exact parts.2
  intro reachable
  have deletionCrosses := (rule.crosses_eq_true _).mpr reachable
  rw [deletionClosed] at deletionCrosses
  contradiction

end
end IGSIII34.Percolation
