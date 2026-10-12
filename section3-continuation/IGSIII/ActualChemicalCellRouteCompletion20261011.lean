import IGSIII.ActualChemicalCellRouteLimit20261011
import IGSIII.Geometry.ActualCellLocalisation

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (ambientLengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
variable (ambientNonnegative : ∀ depth edge, 0 ≤ ambientLengths depth edge)
variable (ambientPositive : ∀ depth edge, configuration depth edge = true → 0 < ambientLengths depth edge)
variable (ambientConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (ambientLengths coarse edge)))
variable (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
variable (anchorRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
variable (componentLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (componentConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) edge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child)))
variable (componentNonnegative : ∀ fine child, 0 ≤ componentLengths fine child)
variable (componentPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge child = true → 0 < componentLengths fine child)


/-- Persistent finite boundary labels are exactly the two completed anchors. -/
theorem rootedComponentVertex_route_boundary20261011 (fine : ℕ) (side : Bool) :
    rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine ((retainedChemicalBoundaryVertex20261011 (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) side) =
      if side then rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence else rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence := by
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rootedFirstBoundaryAnchor]
    rw [← retainedChemicalBoundaryVertex_zero_false20261011]
    simpa only [retainedChemicalBoundaryVertex_persistent20261011] using
      (rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence 0 fine (Nat.zero_le fine)
        (retainedChemicalBoundaryVertex20261011 (rule.generation 0).network
          (generationBlockCells rule coarse 0 (configuration (coarse + 0 + 1)) edge) sourceSide false)).symm
  | true =>
    simp only [↓reduceIte, rootedSecondBoundaryAnchor]
    rw [← retainedChemicalBoundaryVertex_zero_true20261011]
    simpa only [retainedChemicalBoundaryVertex_persistent20261011] using
      (rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence 0 fine (Nat.zero_le fine)
        (retainedChemicalBoundaryVertex20261011 (rule.generation 0).network
          (generationBlockCells rule coarse 0 (configuration (coarse + 0 + 1)) edge) sourceSide true)).symm

/-- Literal first-exit/last-entrance equality on every point of the actual
intrinsic completion. All four boundary routes survive the completion limit. -/
theorem rootedComponentCompletionInclusion_route_equality20261011
    (first last : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) :
    dist (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive first) (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive last) =
      twoBoundaryRouteDistance20261011 (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive)
        (fun side => if side then rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence else rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) first last := by
  have continuousInclusion := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive).continuous
  refine UniformSpace.Completion.induction_on₂ first last (isClosed_eq (by fun_prop)
    (by unfold twoBoundaryRouteDistance20261011; fun_prop)) ?_
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun fine => RetainedComponentVertex (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide)
      (retainedComponentOldEmbedding rule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide))
    (fun fine first last => ?_) first last
  change dist (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine first))
      (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine last)) =
    twoBoundaryRouteDistance20261011 (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive)
      (fun side => if side then rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence else rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)
      (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine first) (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine last)
  have boundaryIdentity :
      (fun side => if side then rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence else rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) =
      (fun side => rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence fine ((retainedChemicalBoundaryVertex20261011 (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) side)) := by
    funext side
    exact (rootedComponentVertex_route_boundary20261011 rule classicalRule configuration coherent scale scalePositive
      coarse edge sourceSide componentLengths componentConvergence componentNonnegative componentPositive fine side).symm
  rw [boundaryIdentity]
  simp only [twoBoundaryRouteDistance20261011, rootedComponentCompletionInclusion_vertex, rootedComponentVertex_distance]
  letI := retainedComponentMetric (rule.generation fine).network (classicalRule.generation fine).simple
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide
    (componentLengths fine) (componentNonnegative fine) (componentPositive fine)
  have intrinsicDistance (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
      dist first last = weightedDistance ((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
        (indexedBondCost (rule.generation fine).network (componentLengths fine)) first.val last.val := rfl
  have finiteIdentity := actualComponentFiniteInclusion_route_equality20261011 rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
    componentLengths componentConvergence componentNonnegative componentPositive fine first last
  simpa only [twoBoundaryRouteDistance20261011, intrinsicDistance] using finiteIdentity

end

section
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


/-- The manuscript cell-route formula for the canonical completed chemical
inclusion, with both actual intrinsic and ambient metrics. -/
theorem actualChemicalCellInclusion_route_equality20261011
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
    (first last : ActualChemicalCellSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide) :
    dist (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained first) (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained last) =
      twoBoundaryRouteDistance20261011 (actualChemicalCellInclusion rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide anchorRetained)
        (fun side => if side then actualChemicalCellSecondBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide else actualChemicalCellFirstBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence coarse edge sourceSide) first last := by
  let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence
  let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  exact rootedComponentCompletionInclusion_route_equality20261011 rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    ambientData.1 ambientData.2.1 ambientData.2.2 coarse edge sourceSide anchorRetained
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.2.2 componentData.1 componentData.2.1 first last


/-- At generation zero the whole cluster includes by the identity, so every
boundary detour is at least the intrinsic direct distance. -/
theorem wholeSpace_twoBoundaryRoute_equality20261011 {Space : Type*} [PseudoMetricSpace Space]
    (boundary : Bool → Space) (first last : Space) :
    dist first last = twoBoundaryRouteDistance20261011 id boundary first last := by
  have routeBound (exit entrance : Bool) :
      dist first last ≤ dist first (boundary exit) + dist (boundary exit) (boundary entrance) + dist (boundary entrance) last := by
    have firstTriangle := dist_triangle first (boundary exit) (boundary entrance)
    have secondTriangle := dist_triangle first (boundary entrance) last
    linarith
  exact le_antisymm
    (le_min le_rfl (le_min (le_min (routeBound false false) (routeBound false true))
      (le_min (routeBound true false) (routeBound true true))))
    (twoBoundaryRouteDistance_le_direct20261011 id boundary first last)

end
end IGSIII.Geometry
