import IGSIII34.Spectral.Collars.WordCellBoundaries
import IGSIII34.Spectral.Collars.CellMassIdentification
import IGSIII34.Spectral.ActualBoundaryTypicalMassCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter
open scoped Topology

local instance chemicalCellMassCompletionMeasurable {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance chemicalCellMassCompletionBorel {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

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

/-- The measure of the genuine completed chemical component is exactly
the original retained-vertex prefix weight. The physical component is the
actual intrinsic continuation image, and the AE preimage equality is
proved from finite ownership and planted-boundary separation. -/
theorem actualChemicalWordComponent_mass_identification
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (actualRatios : ∀ address, Tendsto (fun fine =>
      markedOrientedVertexMass rule marks fine (componentEdgeAddress address)
        (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (fine + address.length) [] .connected)
      atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        ambientData.1 ambientData.2.1 ambientData.2.2)
    (realizationMeasurable : Measurable realization)
    [NullSingletonClass (boundary.map realization)]
    (retainedPaths : ∀ᵐ path ∂boundary, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive)
    (convergence : ∀ᵐ path ∂boundary,
      let ambientData := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing fieldPositive fieldConvergence
      Tendsto (fun depth => actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
        ambientData.1 ambientData.2.1 ambientData.2.2 depth (path (depth + 1))) atTop (𝓝 (realization path))) :
    ∀ depth,
      (∀ word : Fin (depth + 1) → (Fin rule.edges × Bool),
        (boundary.map realization) (actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
          growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word) =
          ENNReal.ofReal (weight (List.ofFn word))) ∧
      (∀ᵐ path ∂boundary, ∀ word : Fin (depth + 1) → (Fin rule.edges × Bool),
        realization path ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
          growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word ↔
          path (depth + 1) = word) := by
  have membership := actualChemicalWordComponent_boundary_membership rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start
    etaNonnegative etaBelowOne coefficientNonnegative radiusBounds boundary realization retainedPaths convergence
  intro depth
  have countableBoundary : (⋃ word : Fin (depth + 1) → (Fin rule.edges × Bool),
      actualChemicalWordComponentBoundary rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word).Countable := by
    apply Set.countable_iUnion
    intro word
    exact (actualChemicalWordComponentBoundary_finite rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word).countable
  have typical : ∀ᵐ path ∂boundary,
      0 < weight (List.ofFn (path (depth + 1))) ∧
      realization path ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
        growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth (path (depth + 1)) := by
    filter_upwards [membership, finite_partition_positive_weight_ae_completion20261011 boundary
      (fun path => path (depth + 1)) (fun word => weight (List.ofFn word)) (atoms (depth + 1))]
      with path member positiveWeight
    exact ⟨positiveWeight, member depth⟩
  apply pushforward_cell_mass_of_ae_prefix_membership boundary realization realizationMeasurable
    (fun path => path (depth + 1)) (fun word => weight (List.ofFn word))
    (fun word => actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth word)
    (fun word => (actualChemicalWordComponent_isClosed rule classicalRule p positive belowOne fixedPoint growth amplitude
      growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence eta coefficient start
      etaNonnegative etaBelowOne coefficientNonnegative radiusBounds depth word).measurableSet)
    _ countableBoundary.measurableSet (countableBoundary.measure_zero (boundary.map realization))
    (atoms (depth + 1)) typical
  intro first last point positiveWeight different firstMember lastMember
  apply Set.mem_iUnion.mpr
  refine ⟨first, ?_⟩
  exact actualChemicalWordComponent_intersection_boundary rule classicalRule p positive belowOne fixedPoint growth amplitude
    growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence depth first last
    weight actualRatios positiveWeight different ⟨firstMember, lastMember⟩

end
end IGSIII34.Spectral
