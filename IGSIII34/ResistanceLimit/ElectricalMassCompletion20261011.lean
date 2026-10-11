import IGSIII34.ResistanceLimit.ElectricalPositiveAnchorsCompletion20261011
import IGSIII.Geometry.BoundaryFullSupport
import IGSIII34.Forms.StationaryWeightMesh

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem exists_actual_electrical_boundary_full_support
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (typical : StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop
        (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (retainedPaths : ∀ᵐ path ∂boundary, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (connectedPositive : ∀ address, retainedComponentState rule marks address = .connected → 0 < weight address)
    (eta coefficient : ℝ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient) (start : ℕ)
    (microscopicMesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
          (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) /
          growth ^ (coarse + fine + 2) ≤ coefficient * eta ^ (coarse + 1))
    (weightStart : ℕ)
    (edgeMesh : ∀ depth, weightStart ≤ depth → ∀ edge,
      stationaryResistance rule p positive belowOne fixedPoint growth value marks depth edge ≤ eta ^ (depth + 1)) :
    ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩,
      Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
      (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ ∧
      (∀ᵐ path ∂boundary, Tendsto (fun depth => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
        growth value growthPositive marks typical depth (path (depth + 1))) atTop (𝓝 (realization path))) ∧
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value
          growthPositive marks typical depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0) := by
  obtain ⟨realization, measurable, probability, convergence, tail, projection⟩ :=
    exists_actual_electrical_component_boundary_pushforward rule p positive belowOne fixedPoint growth value growthPositive
      marks typical fieldLimit boundary retainedPaths eta coefficient etaNonnegative etaBelowOne coefficientNonnegative
      start microscopicMesh
  have denseAnchors := actualElectrical_connected_cylinder_anchors_dense rule p positive belowOne fixedPoint growth value
    growthPositive marks typical (fun depth => eta ^ (depth + 1)) (fun depth => pow_nonneg etaNonnegative _)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)) weightStart edgeMesh
  have fullSupport := boundary_pushforward_full_support boundary (fun _ word => weight (List.ofFn word)) atoms
    (fun depth => depth + start + 1)
    (fun depth word => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks typical (depth + start) word) realization measurable
    (fun depth => coefficient * eta ^ (start + 1) * eta ^ depth / (1 - eta))
    (by simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne)).div_const (1 - eta))
    tail (by
      intro point radius radiusPositive minimum
      obtain ⟨depth, beyond, word, connected, close⟩ := denseAnchors point radius radiusPositive (minimum + start)
      have beyondStart : start ≤ depth := by omega
      refine ⟨depth - start, by omega, ?_⟩
      rw [Nat.sub_add_cancel beyondStart]
      exact ⟨word, connectedPositive _ connected, close⟩)
  exact ⟨realization, measurable, probability, fullSupport.1, fullSupport.2, convergence, projection⟩

end
end IGSIII34.ResistanceLimit
