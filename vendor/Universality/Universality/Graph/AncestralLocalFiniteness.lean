import Universality.Graph.AncestralTowerTail
import Universality.Graph.AncestralInternalNeighborhood
import Universality.Graph.TerminalSpineEscape

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter

theorem Classical.ae_ancestralTower_eventuallyInternal {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age : ℕ) :
    ∀ᵐ address ∂rule.ancestralSpineLaw,
      (rule.ancestralTower age address).EventuallyInternal := by
  have hshift (start : ℕ) : ∀ᵐ address ∂rule.ancestralSpineLaw,
      ∀ vertex : Fin (rule.generation (age + start)).vertices, ∃ n,
        rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
            (rule.generation ((age + start) + n)).network.source ∧
        rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
            (rule.generation ((age + start) + n)).network.target := by
    have hall := ae_all_iff.mpr (fun vertex =>
      h.ae_ancestral_stage_eventually_internal (age + start) vertex)
    exact (rule.ancestralSpine_shift_measurePreserving start).quasiMeasurePreserving.ae hall
  filter_upwards [ae_all_iff.mpr hshift] with address haddress
  apply (rule.ancestralTower age address).eventuallyInternal_of_tails
  intro start
  exact (rule.ancestralTail_eventually_internal_iff age start address).mpr (haddress start)

/-- Almost every genuine ancestral graph is locally finite for every edge
configuration, including the full graph. -/
theorem Classical.ae_ancestralTower_finite_neighborSet {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age : ℕ) :
    ∀ᵐ address ∂rule.ancestralSpineLaw,
      ∀ (configuration : (rule.ancestralTower age address).Edge → Bool)
        (vertex : (rule.ancestralTower age address).Vertex),
        (((rule.ancestralTower age address).openGraph configuration).neighborSet vertex).Finite := by
  filter_upwards [h.ae_ancestralTower_eventuallyInternal age] with address haddress
  exact rule.ancestralTower_finite_neighborSet_of_eventuallyInternal age address haddress

end
end Universality.Rule
