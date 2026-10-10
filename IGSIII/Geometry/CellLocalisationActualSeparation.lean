import IGSIII.Geometry.ActualCellLocalisation
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

variable (coarse : ℕ) (firstEdge secondEdge : Fin (rule.generation coarse).edges) (firstSide secondSide : Bool)
variable (firstRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse firstEdge firstSide))
variable (secondRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse secondEdge secondSide))

/-- Distinct genuine components pay the sum of their intrinsic boundary
radii in the same ambient completion. -/
theorem actualChemicalCellInclusion_boundary_separation (distinct : firstEdge ≠ secondEdge)
    (first : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide)
    (last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide) :
    min (dist first (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide))
      (dist first (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide)) +
    min (dist last (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide))
      (dist last (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide)) ≤
    dist (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide firstRetained first)
      (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide secondRetained last) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let firstData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse firstEdge
  let lastData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse secondEdge
  exact rootedComponentCompletionInclusion_boundary_separation rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse firstEdge secondEdge distinct firstSide secondSide firstRetained secondRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse firstEdge) (markedGenerationConfiguration rule marks coarse [] true firstEdge) (coarse + 1))
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse secondEdge) (markedGenerationConfiguration rule marks coarse [] true secondEdge) (coarse + 1))
    firstData.2.2 lastData.2.2 firstData.1 firstData.2.1 lastData.1 lastData.2.1 first last

/-- Intersections of actual completed cells consist only of shared available
planted vertices, including dangling components. -/
theorem actualChemicalCellInclusion_intersection_boundary (distinct : firstEdge ≠ secondEdge)
    (first : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide)
    (last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide)
    (sameImage : actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide firstRetained first =
      actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide secondRetained last) :
    (first = actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide ∨
      first = actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse firstEdge firstSide) ∧
    (last = actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide ∨
      last = actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse secondEdge secondSide) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let firstData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse firstEdge
  let lastData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse secondEdge
  exact rootedComponentCompletionInclusion_intersection_boundary rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse firstEdge secondEdge distinct firstSide secondSide firstRetained secondRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse firstEdge) (markedGenerationConfiguration rule marks coarse [] true firstEdge) (coarse + 1))
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse secondEdge) (markedGenerationConfiguration rule marks coarse [] true secondEdge) (coarse + 1))
    firstData.2.2 lastData.2.2 firstData.1 firstData.2.1 lastData.1 lastData.2.1 first last sameImage

/-- The two genuine sides of a B socket use the very same noncrossing tower
and length field, and still pay both boundary radii in the ambient metric. -/
theorem actualChemicalCellInclusion_noncrossing_boundary_separation
    (edge : Fin (rule.generation coarse).edges)
    (closed : markedGenerationConfiguration rule marks coarse [] true edge = false)
    (sourceRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge true))
    (targetRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge false))
    (first : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true)
    (last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false) :
    min (dist first (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true))
      (dist first (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true)) +
    min (dist last (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false))
      (dist last (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false)) ≤
    dist (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true sourceRetained first)
      (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false targetRetained last) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_noncrossing_boundary_separation rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 closed targetRetained componentData.1 componentData.2.1 first last

theorem actualChemicalCellInclusion_noncrossing_intersection_boundary
    (edge : Fin (rule.generation coarse).edges)
    (closed : markedGenerationConfiguration rule marks coarse [] true edge = false)
    (sourceRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge true))
    (targetRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge false))
    (first : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true)
    (last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false)
    (sameImage : actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true sourceRetained first =
      actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false targetRetained last) :
    (first = actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true ∨
      first = actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge true) ∧
    (last = actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false ∨
      last = actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge false) := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_noncrossing_intersection_boundary rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 closed targetRetained componentData.1 componentData.2.1 first last sameImage
end
end IGSIII.Geometry
