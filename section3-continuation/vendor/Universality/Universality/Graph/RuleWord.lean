import Universality.Graph.SubstitutionEquivalence
import Universality.Graph.SubstitutionAssociativity
import Universality.Graph.SubstitutionConnectivity

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- A nonempty word of actual rules, with right-associated substitution. -/
def word : List Rule → Rule → Rule
  | [], last => last
  | first :: rest, last => first * word rest last

theorem word_terminalSymmetric (initial : List Rule) (last : Rule)
    (hprefix : ∀ rule ∈ initial, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric) :
    (word initial last).TerminalSymmetric := by
  induction initial with
  | nil => exact hlast
  | cons first rest ih =>
    exact (hprefix first (List.mem_cons_self ..)).mul
      (ih (fun rule hrule => hprefix rule (List.mem_cons_of_mem first hrule)))

theorem word_connected (initial : List Rule) (last : Rule)
    (hprefix : ∀ rule ∈ initial, rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hlast : last.network.fullGraph.Reachable last.network.source last.network.target) :
    (word initial last).network.fullGraph.Reachable
      (word initial last).network.source (word initial last).network.target := by
  induction initial with
  | nil => exact hlast
  | cons first rest ih =>
    exact first.network.substitute_full_connected (word rest last).network
      (hprefix first (List.mem_cons_self ..))
      (ih (fun rule hrule => hprefix rule (List.mem_cons_of_mem first hrule)))

def wordAppendEquivalence (initial : List Rule) (middle : Rule) (suffix : List Rule) (last : Rule) :
    (word (initial ++ middle :: suffix) last).network.NetworkEquivalence
      (word initial middle * word suffix last).network := by
  induction initial with
  | nil => exact NetworkEquivalence.refl _
  | cons first rest ih =>
    exact ((NetworkEquivalence.refl first.network).substitute ih).trans
      (first.network.substitutionAssociativity (word rest middle).network (word suffix last).network).symm

/-- Moving the first factor to the end has the expected block decomposition,
up to the explicit relabelling of the actual finite network. -/
def wordRotateEquivalence (first : Rule) (middle : List Rule) (last : Rule) :
    (word (middle ++ [last]) first).network.NetworkEquivalence
      (word middle last * first).network :=
  wordAppendEquivalence middle last [] first

theorem word_edges (initial : List Rule) (last : Rule) :
    (word initial last).edges = (initial.map Rule.edges).prod * last.edges := by
  induction initial with
  | nil => simp [word]
  | cons first rest ih => simp [word, mul_edges, ih, Nat.mul_assoc]

end
end Universality.Rule
