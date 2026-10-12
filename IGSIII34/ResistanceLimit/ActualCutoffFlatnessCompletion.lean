import IGSIII34.ResistanceLimit.ActualTowerFlatnessCompletion

/-! Constant-cell cutoffs for the actual finite-energy harmonic functions on
the original retained electrical skeleton. Hanging branches and the separate
sides of noncrossing cells are included. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualHarmonicFunction_retained_completion
    (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary
      (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 depth vertex) =
    harmonicTower rule (stationaryConfiguration rule marks.val)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val) marks.property.2
      initial boundary depth bound vertex.val :=
  harmonicTowerFunction_retained rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 initial boundary depth bound vertex

theorem actual_harmonic_function_flat_cell
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (edge : Fin (rule.generation coarse).edges)
    (flatAvailable : stationaryConfiguration rule marks.val coarse edge = true →
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint edge).1 =
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint edge).2)
    (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).Reachable first last)
    (firstRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex first))
    (lastRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex last)) :
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1) ⟨_, firstRetained⟩) =
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1) ⟨_, lastRetained⟩) := by
  rw [actualHarmonicFunction_retained_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    coarse boundary (coarse + fine + 1) (by omega),
    actualHarmonicFunction_retained_completion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary (coarse + fine + 1) (by omega)]
  exact stationary_harmonic_tower_flat_cell rule marks.val
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    growth growthPositive marks.property.1.1.1 marks.property.1.1.2.1 stationary [] true
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    marks.property.2 coarse fine boundary edge flatAvailable first last reachable firstRetained lastRetained

end
end IGSIII34.ResistanceLimit
