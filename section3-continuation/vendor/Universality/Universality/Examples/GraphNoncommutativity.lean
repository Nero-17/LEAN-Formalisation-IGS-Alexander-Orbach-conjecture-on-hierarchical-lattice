import Universality.Graph.Rule
import Universality.Matrix.FullNoncommutativeExample
import Universality.Percolation.WheatstoneSymmetry
import Universality.Percolation.OppositeWheatstoneSymmetry
import Universality.Algebra.MultiplicativeObstruction

/-!
# Two actual finite substitution graphs with different mass growth

This theorem reaches graph-defined conditional mass matrices.  Identification
with infinite-volume critical exponents is a further analytic step and is not
asserted by this module.
-/

namespace Universality
noncomputable section
open FiniteNetwork

def wheatstoneRule : Rule := ⟨4, 5, wheatstoneNetwork⟩
def oppositeWheatstoneRule : Rule := ⟨8, 13, oppositeWheatstoneNetwork⟩

def groupedRule : Rule :=
  ((wheatstoneRule * wheatstoneRule) * oppositeWheatstoneRule) * oppositeWheatstoneRule

def alternatingRule : Rule :=
  ((wheatstoneRule * oppositeWheatstoneRule) * wheatstoneRule) * oppositeWheatstoneRule

theorem wheatstone_reliability_half : wheatstoneNetwork.reliability (1 / 2) = 1 / 2 := by
  norm_num [wheatstone_reliability]

theorem rule_mul_wheatstone_mass (outer : Rule) :
    (outer * wheatstoneRule).network.massMatrix (1 / 2) =
      outer.network.massMatrix (1 / 2) * wheatstoneMassMatrix := by
  rw [Rule.mul_massMatrix outer wheatstoneRule (1 / 2)
    (by change 0 < wheatstoneNetwork.reliability (1 / 2); rw [wheatstone_reliability_half]; norm_num)
    (by change wheatstoneNetwork.reliability (1 / 2) < 1; rw [wheatstone_reliability_half]; norm_num)
    wheatstoneTerminalSymmetry wheatstone_terminal_symmetry_source wheatstone_terminal_symmetry_target]
  change outer.network.massMatrix (wheatstoneNetwork.reliability (1 / 2)) * wheatstoneMassMatrix = _
  rw [wheatstone_reliability_half]

theorem rule_mul_opposite_mass (outer : Rule) :
    (outer * oppositeWheatstoneRule).network.massMatrix (1 / 2) =
      outer.network.massMatrix (1 / 2) * oppositeWheatstoneMassMatrix := by
  rw [Rule.mul_massMatrix outer oppositeWheatstoneRule (1 / 2)
    (by change 0 < oppositeWheatstoneNetwork.reliability (1 / 2); rw [oppositeWheatstone_reliability_half]; norm_num)
    (by change oppositeWheatstoneNetwork.reliability (1 / 2) < 1; rw [oppositeWheatstone_reliability_half]; norm_num)
    oppositeWheatstoneTerminalSymmetry oppositeWheatstone_terminal_symmetry_source
    oppositeWheatstone_terminal_symmetry_target]
  change outer.network.massMatrix (oppositeWheatstoneNetwork.reliability (1 / 2)) *
    oppositeWheatstoneMassMatrix = _
  rw [oppositeWheatstone_reliability_half]

theorem groupedRule_mass : groupedRule.network.massMatrix (1 / 2) = groupedFullMassMatrix := by
  unfold groupedRule
  rw [rule_mul_opposite_mass, rule_mul_opposite_mass, rule_mul_wheatstone_mass]
  rfl

theorem alternatingRule_mass : alternatingRule.network.massMatrix (1 / 2) = alternatingFullMassMatrix := by
  unfold alternatingRule
  rw [rule_mul_opposite_mass, rule_mul_wheatstone_mass, rule_mul_opposite_mass]
  rfl

theorem reordered_rules_edge_counts : groupedRule.edges = 4225 ∧ alternatingRule.edges = 4225 := by
  constructor <;> rfl

theorem reordered_rules_fixed_points :
    groupedRule.network.reliability (1 / 2) = 1 / 2 ∧
      alternatingRule.network.reliability (1 / 2) = 1 / 2 := by
  have ha : wheatstoneRule.network.reliability (1 / 2) = 1 / 2 := wheatstone_reliability_half
  have hb : oppositeWheatstoneRule.network.reliability (1 / 2) = 1 / 2 := oppositeWheatstone_reliability_half
  simp only [groupedRule, alternatingRule, Rule.mul_reliability, ha, hb, and_self]

theorem reordered_graph_mass_spectralRadii_ne :
    spectralRadius ℂ ((groupedRule.network.massMatrix (1 / 2)).map Complex.ofReal) ≠
      spectralRadius ℂ ((alternatingRule.network.massMatrix (1 / 2)).map Complex.ofReal) := by
  rw [groupedRule_mass, alternatingRule_mass]
  exact noncommutative_full_spectralRadii_ne

theorem reordered_graph_multiplicative_observations {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => observations i groupedRule) = (fun i => observations i alternatingRule) := by
  funext i
  simp only [groupedRule, alternatingRule, hmul]
  ac_rfl

theorem no_multiplicative_classification_of_graph_mass {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, observations i (outer * inner) = observations i outer * observations i inner) :
    ¬ ∃ classify : (I → T) → ENNReal, ∀ rule : Rule,
      spectralRadius ℂ ((rule.network.massMatrix (1 / 2)).map Complex.ofReal) =
        classify (fun i => observations i rule) := by
  rintro ⟨classify, hclassify⟩
  apply reordered_graph_mass_spectralRadii_ne
  rw [hclassify, hclassify, reordered_graph_multiplicative_observations observations hmul]

end
end Universality
