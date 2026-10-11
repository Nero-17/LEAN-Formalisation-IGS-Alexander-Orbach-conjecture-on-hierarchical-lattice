import IGSIII34.Spectral.Collars.ChemicalWordCells
import IGSIII34.Topology.DenseClosedImage

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral IGSIII34.Topology MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth amplitude : ℝ) (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
  (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
  (fieldConvergence : ∀ address, Tendsto
    (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
    atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))
  (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)

theorem actualChemicalCellVertex_dense :
    DenseRange (fun point : Σ fine, RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) sourceSide =>
      actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide point.1 point.2) := by
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence coarse edge
  have dense := rootedComponentVertex_dense rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive (coarse + 1)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentData.2.2
  apply dense.mono
  rintro point member
  obtain ⟨fine, vertex, rfl⟩ := Set.mem_iUnion.mp member
  exact ⟨⟨fine, vertex⟩, rfl⟩

theorem actualChemicalCellInclusion_born
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
    (fine : ℕ) (vertex : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) sourceSide) :
    actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained
      (actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide fine vertex) =
    let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    actualComponentFiniteInclusion rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      data.1 data.2.1 data.2.2 coarse edge sourceSide anchorRetained fine vertex := by
  simp only [actualChemicalCellInclusion, actualChemicalCellVertex]
  rw [rootedComponentCompletionInclusion_vertex]

theorem actualChemicalCellInclusion_range_eq_closure_born
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    Set.range (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained) =
    let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    closure (Set.range (fun point : Σ fine, RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) sourceSide =>
      actualComponentFiniteInclusion rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        data.1 data.2.1 data.2.2 coarse edge sourceSide anchorRetained point.1 point.2)) := by
  have embedding := actualChemicalCellInclusion_isClosedEmbedding rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start
    etaNonnegative etaBelowOne coefficientNonnegative radiusBounds coarse edge sourceSide anchorRetained
  rw [range_eq_closure_range_comp_of_dense _
    (actualChemicalCellVertex_dense rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
      value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide)
    _ embedding.continuous embedding.isClosed_range]
  congr 2
  funext point
  exact actualChemicalCellInclusion_born rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained point.1 point.2

theorem actualChemicalWordComponent_eq_closure_born
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (word : Fin (coarse + 1) → Fin rule.edges × Bool)
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive) :
    actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse word =
    let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    closure (Set.range (fun point : Σ fine, RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)
        (generationWordEdge rule coarse (fun index => (word index).1)))
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected =>
      actualComponentFiniteInclusion rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        data.1 data.2.1 data.2.2 coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (retainedComponentState rule marks (List.ofFn word)).sourceSelected
        (actual_word_component_anchor_retained rule marks crossing coarse word live) point.1 point.2)) := by
  unfold actualChemicalWordComponent
  rw [dif_pos live]
  exact actualChemicalCellInclusion_range_eq_closure_born rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse
    (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks (List.ofFn word)).sourceSelected
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    (actual_word_component_anchor_retained rule marks crossing coarse word live)

end
end IGSIII34.ResistanceLimit
