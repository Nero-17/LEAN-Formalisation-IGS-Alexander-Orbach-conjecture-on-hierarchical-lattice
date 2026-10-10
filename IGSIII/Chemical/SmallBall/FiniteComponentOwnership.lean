import IGSIII.Mass.ComponentEmpiricalLaw

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Classical
open scoped BigOperators

variable {Index Source : Type*} {Child : Index → Type*}
variable [Fintype Index] [Fintype Source] [∀ index, Fintype (Child index)]

def finiteComponentOwnership (embedding : (Σ index, Child index) ↪ Source)
    (fallback : Index) (point : Source) : Index :=
  if membership : ∃ child, embedding child = point then (Classical.choose membership).1 else fallback

theorem finiteComponentOwnership_embedding (embedding : (Σ index, Child index) ↪ Source)
    (fallback : Index) (child : Σ index, Child index) :
    finiteComponentOwnership embedding fallback (embedding child) = child.1 := by
  classical
  unfold finiteComponentOwnership
  rw [dif_pos ⟨child, rfl⟩]
  exact congrArg Sigma.fst (embedding.injective (Classical.choose_spec (show ∃ other, embedding other = embedding child from ⟨child, rfl⟩)))

theorem finiteComponentOwnership_outside (embedding : (Σ index, Child index) ↪ Source)
    (fallback : Index) (point : Source) (outside : point ∉ Set.range embedding) :
    finiteComponentOwnership embedding fallback point = fallback := by
  classical
  exact dif_neg outside

def finiteComponentFrontier (embedding : (Σ index, Child index) ↪ Source) : Finset Source :=
  Finset.univ.filter (fun point => point ∉ Set.range embedding)

theorem finiteComponentOwnership_inside (embedding : (Σ index, Child index) ↪ Source)
    (fallback : Index) (point : Source) (inside : point ∉ finiteComponentFrontier embedding) :
    ∃ child : Child (finiteComponentOwnership embedding fallback point),
      embedding ⟨finiteComponentOwnership embedding fallback point, child⟩ = point := by
  classical
  have membership : ∃ child : (Σ index, Child index), embedding child = point := by
    by_contra outside
    exact inside (Finset.mem_filter.mpr ⟨Finset.mem_univ _, outside⟩)
  unfold finiteComponentOwnership
  rw [dif_pos membership]
  exact ⟨(Classical.choose membership).2, Classical.choose_spec membership⟩
theorem finiteComponentOwnership_fiber (embedding : (Σ index, Child index) ↪ Source)
    (fallback index : Index) :
    Finset.univ.filter (fun point => finiteComponentOwnership embedding fallback point = index) =
      Finset.univ.image (fun child : Child index => embedding ⟨index, child⟩) ∪
        if index = fallback then finiteComponentFrontier embedding else ∅ := by
  classical
  ext point
  by_cases membership : point ∈ Set.range embedding
  · obtain ⟨⟨word, child⟩, rfl⟩ := membership
    constructor
    · intro inside
      have equality : word = index := by
        simpa only [finiteComponentOwnership_embedding] using (Finset.mem_filter.mp inside).2
      subst word
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨child, Finset.mem_univ _, rfl⟩)
    · intro inside
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [finiteComponentOwnership_embedding]
      rcases Finset.mem_union.mp inside with imageMembership | frontier
      · obtain ⟨other, _, equality⟩ := Finset.mem_image.mp imageMembership
        exact congrArg Sigma.fst (embedding.injective equality).symm
      · by_cases equality : index = fallback
        · rw [if_pos equality] at frontier
          exact ((Finset.mem_filter.mp frontier).2 ⟨⟨word, child⟩, rfl⟩).elim
        · rw [if_neg equality] at frontier
          exact (Finset.notMem_empty _ frontier).elim
  · constructor
    · intro inside
      have equality : fallback = index := by
        simpa only [finiteComponentOwnership_outside embedding fallback point membership] using (Finset.mem_filter.mp inside).2
      apply Finset.mem_union_right
      rw [if_pos equality.symm]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, membership⟩
    · intro inside
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [finiteComponentOwnership_outside embedding fallback point membership]
      rcases Finset.mem_union.mp inside with imageMembership | frontier
      · obtain ⟨child, _, equality⟩ := Finset.mem_image.mp imageMembership
        exact (membership ⟨⟨index, child⟩, equality⟩).elim
      · by_cases equality : index = fallback
        · exact equality.symm
        · rw [if_neg equality] at frontier
          exact (Finset.notMem_empty _ frontier).elim
theorem finiteComponentOwnership_fiber_card (embedding : (Σ index, Child index) ↪ Source)
    (fallback index : Index) :
    (Finset.univ.filter (fun point => finiteComponentOwnership embedding fallback point = index)).card =
      Fintype.card (Child index) + if index = fallback then (finiteComponentFrontier embedding).card else 0 := by
  classical
  rw [finiteComponentOwnership_fiber, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun first last equality => eq_of_heq (Sigma.mk.inj_iff.mp (embedding.injective equality)).2)]
    simp only [Finset.card_univ]
    split_ifs <;> simp_all
  · apply Finset.disjoint_left.mpr
    intro point imageMembership frontierMembership
    obtain ⟨child, _, rfl⟩ := Finset.mem_image.mp imageMembership
    by_cases equality : index = fallback
    · simp only [if_pos equality, finiteComponentFrontier, Finset.mem_filter, Finset.mem_univ, true_and] at frontierMembership
      exact frontierMembership ⟨⟨index, child⟩, rfl⟩
    · simpa only [if_neg equality, Finset.notMem_empty] using frontierMembership

theorem finiteComponentFrontier_card_partition (embedding : (Σ index, Child index) ↪ Source) :
    Fintype.card Source = (finiteComponentFrontier embedding).card + ∑ index, Fintype.card (Child index) := by
  classical
  have split := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun point : Source => point ∈ Set.range embedding)
  have rangeEquality : Finset.univ.filter (fun point : Source => point ∈ Set.range embedding) = Finset.univ.image embedding := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
  rw [rangeEquality, Finset.card_image_of_injective _ embedding.injective, Finset.card_univ, Finset.card_univ] at split
  rw [Fintype.card_sigma] at split
  exact split.symm.trans (Nat.add_comm _ _)

end
end IGSIII.Geometry