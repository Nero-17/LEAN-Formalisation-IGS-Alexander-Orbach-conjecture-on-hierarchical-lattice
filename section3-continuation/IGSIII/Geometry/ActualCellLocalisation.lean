import IGSIII.Geometry.CellLocalisationEmbedding
import IGSIII.Geometry.CellLocalisationIntersection
import IGSIII.Geometry.CellLocalisationSplitIntersection
import IGSIII.Geometry.CellLocalisationShiftedCompletion
import IGSIII.Geometry.CellLocalisationMarkedCompletionLaw
import IGSIII.Geometry.RootedComponentCompactness
import IGSIII.Geometry.RootedComponentInterior

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology ENNReal

variable (rule : Rule) (classicalRule : rule.Classical)
variable (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
variable (fieldConvergence : ∀ address, Tendsto
  (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
  atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))

/-- The genuine intrinsic component completion in global root units. All
edge lengths and convergence data are derived from the actual terminal field. -/
def ActualChemicalCellSpace (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) : Type :=
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  RootedComponentSpace rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2

instance actualChemicalCellSpaceMetricSpace (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    MetricSpace (ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide) := by
  unfold ActualChemicalCellSpace
  infer_instance

/-- The canonical inclusion into the actual completed root cluster. -/
def actualChemicalCellInclusion (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide →
      let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
        value marks crossing fieldPositive fieldConvergence
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        ambientData.1 ambientData.2.1 ambientData.2.2 := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceSide anchorRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 componentData.1 componentData.2.1

def actualChemicalCellFirstBoundary (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide := by
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedFirstBoundaryAnchor rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2

def actualChemicalCellSecondBoundary (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide := by
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedSecondBoundaryAnchor rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2

theorem actualChemicalCellInclusion_lipschitz (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    LipschitzWith 1 (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_lipschitz rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceSide anchorRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 componentData.1 componentData.2.1

theorem actualChemicalCellInclusion_injective (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    Function.Injective (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_injective rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceSide anchorRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 componentData.1 componentData.2.1

/-- First-exit localisation on every point of the actual completion. -/
theorem actualChemicalCellInclusion_localisation (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
    (first last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide) :
    min (min (dist first (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide))
      (dist first (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide))) (dist first last) ≤
      dist (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained first)
        (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained last) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_localisation rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceSide anchorRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 componentData.1 componentData.2.1 first last

theorem actualChemicalCellSpace_compact
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    CompactSpace (ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide) :=
  actual_component_space_compact_of_terminal_field rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    coarse edge sourceSide

/-- Closed embedding follows from the proved actual component mesh; it is not
an additional hypothesis on the inclusion or the limit space. -/
theorem actualChemicalCellInclusion_isClosedEmbedding
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    Topology.IsClosedEmbedding (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained) := by
  letI := actualChemicalCellSpace_compact rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    coarse edge sourceSide
  exact (actualChemicalCellInclusion_lipschitz rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained).continuous.isClosedEmbedding
    (actualChemicalCellInclusion_injective rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained)
/-- Every original retained finite vertex keeps its label in the actual
intrinsic completed cell. -/
def actualChemicalCellVertex (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (fine : ℕ) (vertex : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) sourceSide) :
    ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide := by
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentVertex rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2 fine vertex

/-- A genuine connected cell has positive intrinsic interior radius at an
original retained vertex. This conclusion is derived from the actual crossing
configuration and strictly positive actual terminal lengths. -/
theorem actualChemicalCellSpace_positive_interior_radius
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (opened : markedGenerationConfiguration rule marks coarse [] true edge = true) :
    ∃ point : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide,
      0 < min (dist point (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide))
        (dist point (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide)) := by
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  have componentCrossing : (rule.generation 0).network.crosses
      (generationBlockCells rule coarse 0 (markedGenerationConfiguration rule marks (coarse + 0 + 1) [] true) edge) = true := by
    rw [generationBlockCells_marked]
    simpa only [List.nil_append, opened] using
      markedGenerationConfiguration_crosses rule marks crossing 0 (generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse [] true edge)
  exact rootedComponentSpace_positive_interior_radius rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2 componentCrossing
end
end IGSIII.Geometry


