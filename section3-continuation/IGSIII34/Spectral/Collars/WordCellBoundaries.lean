import IGSIII34.Spectral.Collars.ChemicalWordCells
import IGSIII34.Spectral.Collars.PositiveWordSlots

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

/-- The available actual planted boundary points of the prefix cell. -/
def actualChemicalWordComponentBoundary (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
    Set (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      ambientData.1 ambientData.2.1 ambientData.2.2) :=
  if live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive then
    {actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
      (generationWordEdge rule depth (fun index => (word index).1))
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (actual_word_component_anchor_retained rule marks crossing depth word live)
      (actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
        (generationWordEdge rule depth (fun index => (word index).1))
        (retainedComponentState rule marks (List.ofFn word)).sourceSelected),
     actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
      (generationWordEdge rule depth (fun index => (word index).1))
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (actual_word_component_anchor_retained rule marks crossing depth word live)
      (actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
        (generationWordEdge rule depth (fun index => (word index).1))
        (retainedComponentState rule marks (List.ofFn word)).sourceSelected)}
  else ∅

theorem actualChemicalWordComponentBoundary_finite
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    (actualChemicalWordComponentBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word).Finite := by
  unfold actualChemicalWordComponentBoundary
  split_ifs
  · exact (Set.finite_singleton _).insert _
  · exact Set.finite_empty

/-- Distinct physical sockets can meet only at the original available
boundary vertices, after completion in the actual chemical metric. -/
theorem actualChemicalWordComponent_distinct_socket_intersection
    (depth : ℕ) (first last : Fin (depth + 1) → (Fin rule.edges × Bool))
    (distinct : generationWordEdge rule depth (fun index => (first index).1) ≠
      generationWordEdge rule depth (fun index => (last index).1)) :
    actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first ∩
      actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth last ⊆
      actualChemicalWordComponentBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first := by
  intro point member
  rcases member with ⟨firstMember, lastMember⟩
  unfold actualChemicalWordComponent at firstMember lastMember
  split_ifs at firstMember with firstLive
  · split_ifs at lastMember with lastLive
    · obtain ⟨firstPoint, firstImage⟩ := firstMember
      obtain ⟨lastPoint, lastImage⟩ := lastMember
      have boundaries := (actualChemicalCellInclusion_intersection_boundary rule classicalRule p positive belowOne fixedPoint
        growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
        _ _ _ _ _ _ distinct firstPoint lastPoint (firstImage.trans lastImage.symm)).1
      unfold actualChemicalWordComponentBoundary
      rw [dif_pos firstLive]
      rcases boundaries with firstBoundary | secondBoundary
      · rw [← firstImage, firstBoundary]
        exact Set.mem_insert _ _
      · rw [← firstImage, secondBoundary]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · exact False.elim lastMember
  · exact False.elim firstMember

theorem actualChemicalCellInclusion_different_sides_intersection_boundary
    (depth : ℕ) (edge lastEdge : Fin (rule.generation depth).edges) (sameEdge : edge = lastEdge)
    (firstSide lastSide : Bool)
    (differentSides : firstSide ≠ lastSide)
    (closed : markedGenerationConfiguration rule marks depth [] true edge = false)
    (firstRetained : ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
      (rule.generation depth).network.source (coarseCellPlantedVertex rule depth edge firstSide))
    (lastRetained : ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
      (rule.generation depth).network.source (coarseCellPlantedVertex rule depth lastEdge lastSide))
    (firstPoint : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth edge firstSide)
    (lastPoint : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth lastEdge lastSide)
    (sameImage : actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth edge firstSide firstRetained firstPoint =
      actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth lastEdge lastSide lastRetained lastPoint) :
    firstPoint = actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth edge firstSide ∨
      firstPoint = actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth edge firstSide := by
  subst lastEdge
  cases firstSide <;> cases lastSide
  · exact (differentSides rfl).elim
  · exact (actualChemicalCellInclusion_noncrossing_intersection_boundary rule classicalRule p positive belowOne fixedPoint
      growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
      edge closed lastRetained firstRetained lastPoint firstPoint sameImage.symm).2
  · exact (actualChemicalCellInclusion_noncrossing_intersection_boundary rule classicalRule p positive belowOne fixedPoint
      growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth
      edge closed firstRetained lastRetained firstPoint lastPoint sameImage).1
  · exact (differentSides rfl).elim

/-- With an actual positive first prefix, every different prefix cell can
meet it only at its available planted boundary. Positivity rules out
duplicate labels by genuine finite interior ownership. -/
theorem actualChemicalWordComponent_intersection_boundary
    (depth : ℕ) (first last : Fin (depth + 1) → (Fin rule.edges × Bool))
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (actualRatios : ∀ address, Tendsto (fun fine =>
      markedOrientedVertexMass rule marks fine (componentEdgeAddress address)
        (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (fine + address.length) [] .connected)
      atTop (𝓝 (weight address)))
    (firstPositive : 0 < weight (List.ofFn first)) (different : first ≠ last) :
    actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first ∩
      actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth last ⊆
      actualChemicalWordComponentBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first := by
  by_cases sameEdge : generationWordEdge rule depth (fun index => (first index).1) =
      generationWordEdge rule depth (fun index => (last index).1)
  · intro point member
    rcases member with ⟨firstMember, lastMember⟩
    unfold actualChemicalWordComponent at firstMember lastMember
    split_ifs at firstMember with firstLive
    · split_ifs at lastMember with lastLive
      · obtain ⟨firstPoint, firstImage⟩ := firstMember
        obtain ⟨lastPoint, lastImage⟩ := lastMember
        have sameEdges : (fun index => (first index).1) = fun index => (last index).1 := by
          apply List.ofFn_injective
          rw [← generationWordEdge_address rule depth, ← generationWordEdge_address rule depth, sameEdge]
        have differentSides : (retainedComponentState rule marks (List.ofFn first)).sourceSelected ≠
            (retainedComponentState rule marks (List.ofFn last)).sourceSelected := by
          intro sameSide
          exact different (actual_positive_component_words_unique_slot rule marks crossing depth first last weight
            actualRatios firstPositive firstLive lastLive sameEdges sameSide)
        have firstBit := generationWordEdge_massOpened rule marks depth [] .connected first firstLive
        have lastBit := generationWordEdge_massOpened rule marks depth [] .connected last lastLive
        change markedGenerationConfiguration rule marks depth [] true
          (generationWordEdge rule depth (fun index => (first index).1)) =
            (retainedComponentState rule marks (List.ofFn first)).massOpened at firstBit
        change markedGenerationConfiguration rule marks depth [] true
          (generationWordEdge rule depth (fun index => (last index).1)) =
            (retainedComponentState rule marks (List.ofFn last)).massOpened at lastBit
        have sourceOfOpened (state : OrientedState) (opened : state.massOpened = true) : state.sourceSelected = true := by
          cases state <;> simp_all [OrientedState.massOpened, OrientedState.sourceSelected]
        have closed : markedGenerationConfiguration rule marks depth [] true
            (generationWordEdge rule depth (fun index => (first index).1)) = false := by
          cases opened : markedGenerationConfiguration rule marks depth [] true
              (generationWordEdge rule depth (fun index => (first index).1)) with
          | false => rfl
          | true =>
            have firstSource := sourceOfOpened _ (firstBit.symm.trans opened)
            have lastSource := sourceOfOpened _ (lastBit.symm.trans (by simpa only [← sameEdge] using opened))
            exact (differentSides (firstSource.trans lastSource.symm)).elim
        have boundaries := actualChemicalCellInclusion_different_sides_intersection_boundary rule classicalRule p positive belowOne
          fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence
          depth _ _ sameEdge _ _ differentSides closed _ _ firstPoint lastPoint (firstImage.trans lastImage.symm)
        unfold actualChemicalWordComponentBoundary
        rw [dif_pos firstLive]
        rcases boundaries with firstBoundary | secondBoundary
        · rw [← firstImage, firstBoundary]
          exact Set.mem_insert _ _
        · rw [← firstImage, secondBoundary]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · exact False.elim lastMember
    · exact False.elim firstMember
  · exact actualChemicalWordComponent_distinct_socket_intersection rule classicalRule p positive belowOne fixedPoint
      growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first last sameEdge

end
end IGSIII34.Spectral
