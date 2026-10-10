import IGSIII34.ResistanceLimit.RadiusSubstitution
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

theorem actual_substitution_terminalResistanceRadius_le
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (radius terminalBound : ℝ) (radiusNonnegative : 0 ≤ radius) (terminalNonnegative : 0 ≤ terminalBound)
    (radiusBound : ∀ edge, terminalResistanceRadius (network inner (configuration edge)) (fun _ => 1) ≤ radius)
    (crossingBound : ∀ edge, inner.crosses (configuration edge) = true →
      unitConfigurationResistance inner (configuration edge) ≤ terminalBound) :
    terminalResistanceRadius (network (outer.substitute inner) (substitutionConfigurationEquiv configuration)) (fun _ => 1) ≤
      radius + outerEdges * terminalBound := by
  calc
    _ = terminalResistanceRadius (substitutedNetwork outer inner configuration) (fun _ => 1) :=
      terminalResistanceRadius_reindex (substitutedNetwork outer inner configuration)
        (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
        (Fintype.equivFin (outer.SubstitutionVertex inner)) (substitutionOpenEdgeEquiv configuration)
        (fun edge => outer.substitute_endpoint inner edge.1 edge.2.val) rfl rfl
        (fun _ => 1) (fun _ => zero_lt_one)
    _ ≤ _ := substituted_terminalResistanceRadius_le outer inner configuration (fun _ => 1) (fun _ => zero_lt_one)
      radius terminalBound radiusNonnegative terminalNonnegative radiusBound crossingBound


end
end IGSIII34.ResistanceLimit

