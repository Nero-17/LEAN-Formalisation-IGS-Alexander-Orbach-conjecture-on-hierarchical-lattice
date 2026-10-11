import IGSIII34.Diffusion.OriginalJointCompactPathEncoding
import IGSIII34.Diffusion.ExtendedJointCompactPathLaw
import IGSIII34.Diffusion.OriginalJointCompactEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction

def originalJointCompactFullState
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space) :
    JointMeasuredMarkedState Space := by
  letI : Nonempty Space := ⟨marks true⟩
  exact (⟨⟨Set.univ, isCompact_univ⟩, Set.univ_nonempty⟩, marks, masses)

/-- The original encoding retains the full geometric carrier. Its image
in the extended representative type is exactly the compact-space state
encoding, including the same marks, masses and entire path. -/
theorem originalJointCompactPathRepresentative_toExtended
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    ExtendedJointCompactRepresentative.ofOriginal
        (OriginalJointCompactRepresentative.ofCompactSpace marks masses path) =
      ExtendedJointCompactRepresentative.ofCompactSpace
        (originalJointCompactFullState marks masses) path := by
  letI : Nonempty Space := ⟨marks true⟩
  let compact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding Space
  let embedding : Space ≃ᵢ compact := (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  have fullImage : (⟨⟨Set.univ, isCompact_univ⟩, Set.univ_nonempty⟩ : NonemptyCompacts Space).map
      embedding embedding.continuous =
        (⟨⟨Set.univ, isCompact_univ⟩, Set.univ_nonempty⟩ : NonemptyCompacts compact) := by
    apply NonemptyCompacts.ext
    change embedding '' Set.univ = Set.univ
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr embedding.surjective
  have states : originalJointRepresentativeState
      (OriginalJointCompactRepresentative.ofCompactSpace marks masses path) =
      jointMeasuredMarkedStateMap embedding embedding.continuous
        (originalJointCompactFullState marks masses) := by
    apply Prod.ext
    · exact fullImage.symm
    · rfl
  change ({
    ambient := compact
    state := originalJointRepresentativeState
      (OriginalJointCompactRepresentative.ofCompactSpace marks masses path)
    path := skorokhodCadlagContinuousCarrierMapCompletion20261011 embedding embedding.continuous path } :
      ExtendedJointCompactRepresentative) =
    ({
      ambient := compact
      state := jointMeasuredMarkedStateMap embedding embedding.continuous
        (originalJointCompactFullState marks masses)
      path := skorokhodCadlagContinuousCarrierMapCompletion20261011 embedding embedding.continuous path } :
      ExtendedJointCompactRepresentative)
  rw [states]

theorem originalJointCompactPathRepresentative_extended_class
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    extendedJointCompactClass (.ofOriginal (.ofCompactSpace marks masses path)) =
      extendedJointStatePathClass (originalJointCompactFullState marks masses) path :=
  congrArg extendedJointCompactClass
    (originalJointCompactPathRepresentative_toExtended marks masses path)

theorem originalJointCompactPathEncoding_toExtended
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    originalJointCompactSpaceToExtended (originalJointCompactPathEncoding marks masses path) =
      extendedJointStatePathClass (originalJointCompactFullState marks masses) path := by
  rw [originalJointCompactPathEncoding, originalJointCompactSpaceToExtended_class]
  exact originalJointCompactPathRepresentative_extended_class marks masses path


end
end IGSIII34.Diffusion
