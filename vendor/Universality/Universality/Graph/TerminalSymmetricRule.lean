import Universality.Graph.Rule
import Universality.Graph.SubstitutionSymmetry

namespace Universality.Rule
noncomputable section

def TerminalSymmetric (rule : Rule) : Prop :=
  ∃ symmetry : rule.network.NetworkSymmetry,
    symmetry.vertex rule.network.source = rule.network.target ∧
      symmetry.vertex rule.network.target = rule.network.source

theorem TerminalSymmetric.mul {outer inner : Rule}
    (houter : outer.TerminalSymmetric) (hinner : inner.TerminalSymmetric) :
    (outer * inner).TerminalSymmetric := by
  obtain ⟨outerSymmetry, hsource, htarget⟩ := houter
  obtain ⟨innerSymmetry, hsource', htarget'⟩ := hinner
  exact ⟨outerSymmetry.substitute innerSymmetry hsource' htarget',
    outerSymmetry.substitute_source innerSymmetry hsource' htarget' hsource,
    outerSymmetry.substitute_target innerSymmetry hsource' htarget' htarget⟩

end
end Universality.Rule
