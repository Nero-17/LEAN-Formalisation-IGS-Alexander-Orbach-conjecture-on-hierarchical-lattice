import IGSIII.Geometry.RootedComponentNets
import IGSIII.Geometry.GenericComponentLengths

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology ENNReal

/-- Every genuine planted component is intrinsically compact in root units.
Both the component metric and its finite nets come from the actual replacement
configuration. The assertion includes either side of a noncrossing cell. -/
theorem actual_component_space_compact_of_terminal_field
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
    (fieldConvergence : ∀ address, Tendsto
      (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    let componentConfiguration := fun fine => generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge
    let componentLengths := chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1)
    let componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
      value marks crossing fieldPositive fieldConvergence coarse edge
    CompactSpace (RootedComponentSpace rule classicalRule componentConfiguration
      (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
      sourceSide growth growthPositive (coarse + 1) componentLengths componentData.1 componentData.2.1 componentData.2.2) := by
  dsimp only
  have componentData := actual_component_block_lengths rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence coarse edge
  have configurationIdentity (fine : ℕ) :
      generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge =
        markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse [] true edge) := by
    simpa only [List.nil_append] using generationBlockCells_marked rule marks coarse fine [] true edge
  have componentConvergence : ∀ age child, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule age fine
          (generationBlockCells rule coarse (age + fine + 1)
            (markedGenerationConfiguration rule marks (coarse + (age + fine + 1) + 1) [] true) edge) child)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        growth ^ (age + fine + 2 + (generationEdgeAddress rule coarse edge).length)) atTop
      (𝓝 (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
        (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1) age child)) := by
    simpa only [generationEdgeAddress_length] using componentData.2.2
  have compactness := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule
    (fun fine => generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)
    (generationBlockCells_sequence_coherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent coarse edge)
    sourceSide growth growthPositive marks (generationEdgeAddress rule coarse edge)
    (markedGenerationConfiguration rule marks coarse [] true edge) configurationIdentity
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1))
    componentData.1 componentData.2.1 componentConvergence eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  exact compactness

end
end IGSIII.Geometry

