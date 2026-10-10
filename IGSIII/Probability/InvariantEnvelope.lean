import Mathlib.Order.Iterate
import Mathlib.Order.Bounds.Basic

set_option autoImplicit false

namespace IGSIII.Probability

open Set

theorem map_glb_le_of_onto {Space : Type*} [PartialOrder Space]
    (map : Space → Space) (monotone : Monotone map) (family : Set Space)
    (onto : Set.SurjOn map family family) (envelope : Space)
    (greatestLowerBound : IsGLB family envelope) : map envelope ≤ envelope := by
  apply greatestLowerBound.2
  intro value member
  obtain ⟨predecessor, predecessorMember, equality⟩ := onto member
  rw [← equality]
  exact monotone (greatestLowerBound.1 predecessorMember)

theorem antitone_iterates_of_invariant_glb {Space : Type*} [PartialOrder Space]
    (map : Space → Space) (monotone : Monotone map) (family : Set Space)
    (onto : Set.SurjOn map family family) (envelope : Space)
    (greatestLowerBound : IsGLB family envelope) :
    Antitone (fun depth : ℕ => map^[depth] envelope) :=
  monotone.antitone_iterate_of_map_le
    (map_glb_le_of_onto map monotone family onto envelope greatestLowerBound)

theorem iterate_mem_of_invariant {Space : Type*} (map : Space → Space)
    (family : Set Space) (invariant : Set.MapsTo map family family)
    (value : Space) (member : value ∈ family) (depth : ℕ) : map^[depth] value ∈ family := by
  induction depth with
  | zero => exact member
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply']
    exact invariant inductionHypothesis

end IGSIII.Probability
