import IGSIII34.ResistanceLimit.RadiusNumbered
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem networkEquivalence_terminalResistanceRadius
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges) :
    terminalResistanceRadius (network second (equivalence.configuration configuration)) (fun _ => 1) =
      terminalResistanceRadius (network first configuration) (fun _ => 1) := by
  exact terminalResistanceRadius_reindex (network first configuration)
    (network second (equivalence.configuration configuration)) equivalence.vertex
    (networkEquivalenceOpenEdges equivalence configuration) (fun edge => equivalence.endpoint edge.val)
    equivalence.source.symm equivalence.target.symm (fun _ => 1) (fun _ => zero_lt_one)

def markedElectricalRadius (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) : ℝ :=
  terminalResistanceRadius (network (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth address opened)) (fun _ => 1)


theorem markedElectricalRadius_succ_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (radius terminalBound : ℝ) (radiusNonnegative : 0 ≤ radius) (terminalNonnegative : 0 ≤ terminalBound)
    (radiusBound : ∀ edge, markedElectricalRadius rule marks depth (address ++ [edge]) (marks (address, opened) edge) ≤ radius)
    (terminalBounds : ∀ edge, unitConfigurationResistance (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)) ≤ terminalBound) :
    markedElectricalRadius rule marks (depth + 1) address opened ≤ radius + rule.edges * terminalBound := by
  have transport := networkEquivalence_terminalResistanceRadius (rule.generationTopDecomposition depth)
    (markedGenerationConfiguration rule marks (depth + 1) address opened)
  have configurationIdentity : (rule.generationTopDecomposition depth).configuration
      (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks depth
        (address ++ [edge]) (marks (address, opened) edge)) :=
    (rule.generationTopDecomposition depth).configuration.apply_symm_apply _
  calc
    _ = terminalResistanceRadius (network (rule.network.substitute (rule.generation depth).network)
        (substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks depth
          (address ++ [edge]) (marks (address, opened) edge)))) (fun _ => 1) := by
      exact transport.symm.trans (congrArg (fun configuration =>
        terminalResistanceRadius (network (rule.network.substitute (rule.generation depth).network) configuration)
          (fun _ => 1)) configurationIdentity)
    _ ≤ _ := actual_substitution_terminalResistanceRadius_le rule.network (rule.generation depth).network _
      radius terminalBound radiusNonnegative terminalNonnegative radiusBound (fun edge _ => terminalBounds edge)

end
end IGSIII34.ResistanceLimit


