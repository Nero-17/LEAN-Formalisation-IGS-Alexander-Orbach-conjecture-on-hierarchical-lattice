import IGSIII.Probability.OmegaOrbit

set_option autoImplicit false

namespace IGSIII.Probability

theorem exists_iterated_predecessor {Space : Type*} (map : Space → Space)
    (family : Set Space) (onto : Set.SurjOn map family family)
    (value : Space) (member : value ∈ family) (depth : ℕ) :
    ∃ predecessor ∈ family, map^[depth] predecessor = value := by
  induction depth generalizing value with
  | zero => exact ⟨value, member, rfl⟩
  | succ depth inductionHypothesis =>
    obtain ⟨immediate, immediateMember, immediateIdentity⟩ := onto member
    obtain ⟨predecessor, predecessorMember, identity⟩ := inductionHypothesis immediate immediateMember
    refine ⟨predecessor, predecessorMember, ?_⟩
    rw [Function.iterate_succ_apply', identity, immediateIdentity]

end IGSIII.Probability
