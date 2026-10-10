import Universality.Graph.AncestralBallShapes
namespace Universality
open Filter

theorem eventualPredicate_iff_of_eventually_iff (predicate : ℕ → Prop) (limitPredicate : Prop)
    (hstable : ∀ᶠ n in atTop, predicate n ↔ limitPredicate) :
    (∃ first, ∀ n, first ≤ n → predicate n) ↔ limitPredicate := by
  rw [← eventually_atTop]
  constructor
  · intro heventual
    obtain ⟨n, hn, hevent⟩ := (hstable.and heventual).exists
    exact hn.mp hevent
  · intro hlimit
    exact hstable.mono (fun _ hn => hn.mpr hlimit)

end Universality

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- A countable measurable representation of the eventual full-ball shape.
The next theorem identifies it almost surely with the actual graph ball. -/
def uniformRootEventualFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target)
    (sample : rule.UniformRootSample) : Prop :=
  ∃ first, ∀ n, first ≤ n → sample.2 ∈
    rule.ancestralStageFullBallShape radius targetGraph targetRoot sample.1 n

theorem measurableSet_uniformRootEventualFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    MeasurableSet {sample | rule.uniformRootEventualFullBallShape radius targetGraph targetRoot sample} := by
  apply (Universality.measurableSet_ageSample_iff _).mpr
  intro age
  change MeasurableSet {sample : rule.AncestralSample age | ∃ first, ∀ n, first ≤ n →
    sample ∈ rule.ancestralStageFullBallShape radius targetGraph targetRoot age n}
  simp only [Set.setOf_exists, Set.setOf_forall]
  exact MeasurableSet.iUnion (fun first => MeasurableSet.iInter (fun n =>
    MeasurableSet.iInter (fun _ => rule.measurableSet_ancestralStageFullBallShape
      radius targetGraph targetRoot age n)))

theorem Classical.ae_ancestral_eventualFullBallShape_iff {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (age radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    ∀ᵐ sample ∂rule.ancestralSampleLaw age p,
      rule.uniformRootEventualFullBallShape radius targetGraph targetRoot ⟨age, sample⟩ ↔
        rule.uniformRootFullBallShape radius targetGraph targetRoot ⟨age, sample⟩ := by
  filter_upwards [h.ae_ancestral_fullBallShape_stabilizes p age radius targetGraph targetRoot]
    with sample hsample
  exact eventualPredicate_iff_of_eventually_iff _ _ hsample

theorem Classical.ae_uniformRoot_eventualFullBallShape_iff {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    ∀ᵐ sample ∂rule.uniformRootSampleLaw h.edges_gt_one p,
      rule.uniformRootEventualFullBallShape radius targetGraph targetRoot sample ↔
        rule.uniformRootFullBallShape radius targetGraph targetRoot sample := by
  filter_upwards [h.ae_uniformRoot_finite_neighborSet p] with sample hsample
  have hstable := h.ancestral_fullBallShape_stabilizes_of_finite_neighbors
    sample.1 radius sample.2 targetGraph targetRoot (hsample (fun _ => true))
  exact eventualPredicate_iff_of_eventually_iff _ _ hstable

end
end Universality.Rule
