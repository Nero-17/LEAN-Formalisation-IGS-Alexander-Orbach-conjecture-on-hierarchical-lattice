import IGSIII34.Spectral.ActualDescendantAnchorCompletion
import IGSIII34.ResistanceLimit.ActualAvailableCellCoverCompletion
import IGSIII34.ResistanceLimit.HarmonicTowerBlockMinimumCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

/-- A coarse component whose available roots have the same boundary value
has this value at every genuinely retained descendant cylinder anchor. -/
theorem actual_component_prefix_harmonic_anchor_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool))
    (parentLive : retainedComponentState rule marks.val (List.ofFn parentWord) ≠ .inactive)
    (live : retainedComponentState rule marks.val
      (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix)) ≠ .inactive)
    (flatAvailable : stationaryConfiguration rule marks.val coarse
      (generationWordEdge rule coarse (fun index => (parentWord index).1)) = true →
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).1 =
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).2) :
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1)
        ⟨componentWordAnchor rule marks.val (coarse + fine + 1)
            (blockWordAppendCompletion coarse fine parentWord suffix),
          componentWordAnchor_retained rule marks.val marks.property.1.1.2.1 _ _ live⟩) =
      boundary (componentWordAnchor rule marks.val coarse parentWord) := by
  have parentRetained := componentWordAnchor_retained rule marks.val marks.property.1.1.2.1 coarse parentWord parentLive
  have plantedIdentity :
      (generationBlockCellEmbedding rule coarse fine
        (generationWordEdge rule coarse (fun index => (parentWord index).1))).vertex
        (plantedVertex (rule.generation fine).network
          (retainedComponentState rule marks.val (List.ofFn parentWord)).sourceSelected) =
      blockOldVertexEmbedding rule coarse fine (componentWordAnchor rule marks.val coarse parentWord) := by
    unfold componentWordAnchor
    cases side : (retainedComponentState rule marks.val (List.ofFn parentWord)).sourceSelected <;>
      simp only [plantedVertex, side, Bool.false_eq_true, ↓reduceIte]
    · exact generationBlockCellEmbedding_target rule coarse fine _
    · exact generationBlockCellEmbedding_source rule coarse fine _
  have firstRetained :
      ((rule.generation (coarse + fine + 1)).network.openGraph
        (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).vertex
          (plantedVertex (rule.generation fine).network
            (retainedComponentState rule marks.val (List.ofFn parentWord)).sourceSelected)) := by
    rw [plantedIdentity]
    exact (actual_block_old_retained_iff rule marks.val marks.property.1.1.2.1 coarse fine [] true _).mpr parentRetained
  have lastRetained := componentWordAnchor_retained rule marks.val marks.property.1.1.2.1
    (coarse + fine + 1) (blockWordAppendCompletion coarse fine parentWord suffix) live
  rw [component_descendant_anchor_block_identity_completion] at lastRetained
  have flat := actual_harmonic_function_flat_cell rule p positive belowOne fixedPoint growth value growthPositive marks
    stationary coarse fine boundary (generationWordEdge rule coarse (fun index => (parentWord index).1)) flatAvailable
    _ _ (actual_component_descendant_anchor_local_reachable_completion rule marks.val
      marks.property.1.1.2.1 coarse fine parentWord suffix parentLive live) firstRetained lastRetained
  have firstValue :
      actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
        (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
          (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
          (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1) ⟨_, firstRetained⟩) =
        boundary (componentWordAnchor rule marks.val coarse parentWord) := by
    rw [actualHarmonicFunction_retained_completion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary (coarse + fine + 1) (by omega)]
    dsimp only at ⊢
    rw [plantedIdentity]
    exact harmonicTower_block_boundary rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val) marks.property.2
      coarse fine boundary ⟨_, parentRetained⟩
  simpa only [← component_descendant_anchor_block_identity_completion] using flat.symm.trans firstValue

end
end IGSIII34.Spectral
