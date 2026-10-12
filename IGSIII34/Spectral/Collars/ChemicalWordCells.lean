import IGSIII.Geometry.CellLocalisationActualSeparation
import IGSIII.Geometry.ActualComponentBoundary
import IGSIII34.Spectral.NoncollarPathSuffixCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter
open scoped Topology

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

include crossing in
theorem actual_word_component_anchor_retained (depth : ℕ)
    (word : Fin (depth + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive) :
    ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
      (rule.generation depth).network.source
      (coarseCellPlantedVertex rule depth (generationWordEdge rule depth (fun index => (word index).1))
        (retainedComponentState rule marks (List.ofFn word)).sourceSelected) := by
  simpa only [coarseCellPlantedVertex, componentWordAnchor] using
    componentWordAnchor_retained rule marks crossing depth word live

/-- The physical closed component attached to an actual split prefix.
Its points are the image of the genuine intrinsic continuation completion;
the two B sides retain their original common innovations. -/
def actualChemicalWordComponent (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    Set (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      ambientData.1 ambientData.2.1 ambientData.2.2) :=
  if live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive then
    Set.range (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
      (generationWordEdge rule depth (fun index => (word index).1))
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (actual_word_component_anchor_retained rule marks crossing depth word live))
  else ∅

theorem actualChemicalWordComponent_isClosed
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    IsClosed (actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word) := by
  unfold actualChemicalWordComponent
  split_ifs with live
  · exact (actualChemicalCellInclusion_isClosedEmbedding rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start
      etaNonnegative etaBelowOne coefficientNonnegative radiusBounds depth _ _ _).isClosed_range
  · exact isClosed_empty

/-- Every actual descendant anchor lies in the physical component
specified by its prefix, before taking any boundary limit. -/
theorem actualChemicalWordComponent_descendant_anchor
    (coarse fine : ℕ) (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool))
    (prefixLive : retainedComponentState rule marks (List.ofFn parentWord) ≠ .inactive)
    (live : retainedComponentState rule marks
      (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix)) ≠ .inactive) :
    let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      ambientData.1 ambientData.2.1 ambientData.2.2 (coarse + fine + 1)
        (blockWordAppendCompletion coarse fine parentWord suffix) ∈
      actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse parentWord := by
  dsimp only
  unfold actualChemicalWordComponent
  rw [dif_pos prefixLive]
  let localAnchor : Fin (rule.generation fine).vertices :=
    if (retainedComponentState rule marks
        (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix))).sourceSelected then
      ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).1
    else ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).2
  have localRetained := actual_component_descendant_anchor_local_reachable_completion
    rule marks crossing coarse fine parentWord suffix prefixLive live
  refine ⟨actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse
    (generationWordEdge rule coarse (fun index => (parentWord index).1))
    (retainedComponentState rule marks (List.ofFn parentWord)).sourceSelected fine ⟨localAnchor, localRetained⟩, ?_⟩
  simp only [actualChemicalCellInclusion, actualChemicalCellVertex]
  rw [rootedComponentCompletionInclusion_vertex]
  unfold actualComponentFiniteInclusion actualComponentWordPoint
  rw [dif_pos live]
  apply congrArg
  apply Subtype.ext
  exact (component_descendant_anchor_block_identity_completion rule marks coarse fine parentWord suffix).symm

/-- The original boundary realization lies in its actual physical closed
prefix component, simultaneously at every finite generation. -/
theorem actualChemicalWordComponent_boundary_membership
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        ambientData.1 ambientData.2.1 ambientData.2.2)
    (retainedPaths : ∀ᵐ path ∂boundary, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive)
    (convergence : ∀ᵐ path ∂boundary,
      let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
      Tendsto (fun depth => actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        ambientData.1 ambientData.2.1 ambientData.2.2 depth (path (depth + 1))) atTop (𝓝 (realization path))) :
    ∀ᵐ path ∂boundary, ∀ depth,
      realization path ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth (path (depth + 1)) := by
  filter_upwards [retainedPaths, convergence] with path retained converges
  intro depth
  have closed := actualChemicalWordComponent_isClosed rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start
    etaNonnegative etaBelowOne coefficientNonnegative radiusBounds depth (path (depth + 1))
  apply closed.mem_of_tendsto (converges.comp (tendsto_add_atTop_nat (depth + 1)))
  apply Eventually.of_forall
  intro fine
  obtain ⟨suffix, decomposition⟩ := nested_path_block_decomposition_completion path
    (fun depth => (retained depth).1) depth fine
  have member := actualChemicalWordComponent_descendant_anchor rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth fine (path (depth + 1)) suffix
    (retained (depth + 1)).2 (by rw [← decomposition]; exact (retained (depth + fine + 2)).2)
  rw [← decomposition] at member
  dsimp only [Function.comp_def]
  rw [show fine + (depth + 1) = depth + fine + 1 by omega]
  simpa only [show depth + fine + 1 + 1 = depth + fine + 2 by omega] using member

end
end IGSIII34.Spectral
