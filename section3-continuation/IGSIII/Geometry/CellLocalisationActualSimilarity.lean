import IGSIII.Geometry.ActualCellLocalisation
import IGSIII.Geometry.CellLocalisationShiftData
import IGSIII.Geometry.CellLocalisationConfigurationSimilarity

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory Filter
open scoped Topology ENNReal

/-- Exact original vertex labels identify a shifted-root tower with its actual
indexed block cell. -/
theorem shiftedRoot_cell_configuration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
    (fun fine => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
      fine [] (markedGenerationConfiguration rule marks coarse [] true edge)) =
    (fun fine => generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) := by
  funext fine
  rw [markedGenerationConfiguration_shift]
  simpa only [List.append_nil, List.nil_append] using (generationBlockCells_marked rule marks coarse fine [] true edge).symm
variable (rule : Rule) (classicalRule : rule.Classical)
variable (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (coherent : ∀ address opened, configurationSequenceCoherent rule
  (fun depth => markedGenerationConfiguration rule marks depth address opened))
variable (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
variable (fieldConvergence : ∀ address, Tendsto
  (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
  atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))

/-- Every actual intrinsic descendant completion is a canonical similarity
copy of the completed root model on its actual shifted C/N innovation tree. -/
def actualChemicalCellSimilarity (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge)) (innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge)) (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge) sourceSide 0 ≃ᵤ
      ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing (coherent [] true) fieldPositive fieldConvergence coarse edge sourceSide := by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0
  let lastData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionSimilarityOfConfiguration rule classicalRule
    (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) depth [] (markedGenerationConfiguration rule marks coarse [] true edge))
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    ((innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge)) (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) (coherent [] true) coarse edge) sourceSide growth growthPositive 0 (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2
    (shiftedRoot_cell_configuration rule marks coarse edge)
    (growth ^ (coarse + 1))⁻¹ (inv_pos.mpr (pow_pos growthPositive (coarse + 1)))
    (chemicalAddressBlockLimitLength_shift_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))

theorem actualChemicalCellSimilarity_distance (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (first last : ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge)) (innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge)) (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge) sourceSide 0) :
    dist (actualChemicalCellSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide first)
      (actualChemicalCellSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide last) =
      (growth ^ (coarse + 1))⁻¹ * dist first last := by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0
  let lastData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionSimilarityOfConfiguration_distance rule classicalRule
    (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) depth [] (markedGenerationConfiguration rule marks coarse [] true edge))
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    ((innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge)) (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) (coherent [] true) coarse edge) sourceSide growth growthPositive 0 (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2
    (shiftedRoot_cell_configuration rule marks coarse edge)
    (growth ^ (coarse + 1))⁻¹ (inv_pos.mpr (pow_pos growthPositive (coarse + 1)))
    (chemicalAddressBlockLimitLength_shift_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1)) first last

/-- The full completed similarity preserves each original finite vertex
label, including planted terminal labels and every later persistent label. -/
theorem actualChemicalCellSimilarity_vertex
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
        fine [] (markedGenerationConfiguration rule marks coarse [] true edge)) sourceSide) :
    let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
      value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
      (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge))
      (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge))
      (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge))
      [] (markedGenerationConfiguration rule marks coarse [] true edge) 0
    actualChemicalCellSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide
      (rootedComponentVertex rule classicalRule
        (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
          depth [] (markedGenerationConfiguration rule marks coarse [] true edge))
        ((innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge))
        sourceSide growth growthPositive 0
        (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value
          (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0)
        firstData.1 firstData.2.1 firstData.2.2 fine vertex) =
    actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
      value marks crossing (coherent [] true) fieldPositive fieldConvergence coarse edge sourceSide fine
      (retainedComponentVertexConfigurationEquiv rule
        (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
          depth [] (markedGenerationConfiguration rule marks coarse [] true edge))
        (fun depth => generationBlockCells rule coarse depth (markedGenerationConfiguration rule marks (coarse + depth + 1) [] true) edge)
        (shiftedRoot_cell_configuration rule marks coarse edge) sourceSide fine vertex) := by
  dsimp only
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks)
    (innovationTreeShift_crossing rule marks crossing (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive (generationEdgeAddress rule coarse edge))
    (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence (generationEdgeAddress rule coarse edge))
    [] (markedGenerationConfiguration rule marks coarse [] true edge) 0
  let lastData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionSimilarityOfConfiguration_vertex rule classicalRule
    (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) depth [] (markedGenerationConfiguration rule marks coarse [] true edge))
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    ((innovationTreeShift_coherent rule marks coherent (generationEdgeAddress rule coarse edge)) [] (markedGenerationConfiguration rule marks coarse [] true edge)) (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) (coherent [] true) coarse edge) sourceSide growth growthPositive 0 (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value (innovationTreeShift rule (generationEdgeAddress rule coarse edge) marks) [] (markedGenerationConfiguration rule marks coarse [] true edge) 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2
    (shiftedRoot_cell_configuration rule marks coarse edge)
    (growth ^ (coarse + 1))⁻¹ (inv_pos.mpr (pow_pos growthPositive (coarse + 1)))
    (chemicalAddressBlockLimitLength_shift_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1)) fine vertex
end
end IGSIII.Geometry




