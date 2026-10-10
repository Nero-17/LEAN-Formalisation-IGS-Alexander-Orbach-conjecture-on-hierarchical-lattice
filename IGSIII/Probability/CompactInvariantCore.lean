import IGSIII.Probability.CountableInvariantFamily
import IGSIII.Probability.CompactApproximation

set_option autoImplicit false

namespace IGSIII.Probability

open Set TopologicalSpace

theorem exists_countable_invariant_subset {Space : Type*} [MetricSpace Space]
    (map : Space → Space) (container : Set Space) (nonempty : container.Nonempty)
    (compact : IsCompact container) (forward : Set.MapsTo map container container)
    (onto : Set.SurjOn map container container) :
    ∃ core : Set Space, core.Countable ∧ core.Nonempty ∧ core ⊆ container ∧
      Set.MapsTo map core core ∧ Set.SurjOn map core core := by
  classical
  letI : Nonempty container := nonempty.to_subtype
  letI : SeparableSpace container := compact.isSeparable.separableSpace
  let restricted : container → container := fun value => ⟨map value, forward value.property⟩
  have restrictedOnto : Function.Surjective restricted := by
    intro value
    obtain ⟨predecessor, member, equality⟩ := onto value.property
    exact ⟨⟨predecessor, member⟩, Subtype.ext equality⟩
  obtain ⟨subcore, countable, dense, invariant, surjective⟩ :=
    exists_countable_dense_invariant_core restricted restrictedOnto
  let core : Set Space := Subtype.val '' subcore
  have subcoreNonempty : subcore.Nonempty := dense.nonempty
  refine ⟨core, countable.image _, subcoreNonempty.image _, ?_, ?_, ?_⟩
  · rintro value ⟨lift, _, rfl⟩
    exact lift.property
  · rintro value ⟨lift, member, rfl⟩
    exact ⟨restricted lift, invariant member, rfl⟩
  · rintro value ⟨lift, member, rfl⟩
    obtain ⟨predecessor, predecessorMember, equality⟩ := surjective member
    exact ⟨predecessor, ⟨predecessor, predecessorMember, rfl⟩,
      congrArg Subtype.val equality⟩

end IGSIII.Probability
