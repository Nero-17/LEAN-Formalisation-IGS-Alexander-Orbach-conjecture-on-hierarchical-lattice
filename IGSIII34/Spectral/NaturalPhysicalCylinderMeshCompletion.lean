import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import IGSIII34.Spectral.PhysicalElectricalInverseMaximaCompletion
import IGSIII34.ResistanceLimit.RadiusMesh
import IGSIII34.ResistanceLimit.ElectricalBoundaryCompletion
import IGSIII34.ResistanceLimit.ElectricalMassCompletion
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- The original unit-edge radius mesh controls the same physical
stationary space used by the energy and diffusion limits. The realization
is arbitrary among genuine limits of its actual component anchors. -/
theorem natural_physical_boundary_anchor_mesh_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreater : 1 < natural.growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ threshold : ℕ,
      ∀ (typical : StationaryElectricalTypical rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) marks),
      ∀ (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (retainedPaths : ∀ᵐ path ∂boundaryLaw, ∀ depth,
          Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive),
      ∀ (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)
        (convergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
          actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical depth (path (depth + 1)))
          atTop (𝓝 (realization path))),
      ∀ᵐ path ∂boundaryLaw, ∀ depth : ℕ, threshold ≤ depth →
        dist (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical depth (path (depth + 1)))
          (realization path) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)^2) * eta^(depth + 1) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  filter_upwards [ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      fixed membership eta etaPositive etaBelowOne productGreater,
    natural.almostSure, natural_physical_electrical_field_scaling_completion rule p positive belowOne fixedPoint natural]
      with marks mesh actualLimit scaling
  obtain ⟨threshold, radiusBounds⟩ := mesh
  have fieldLimit : ∀ address, Tendsto (fun depth => natural.growth⁻¹^depth * electricalIteration rule marks depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks)) := by
    intro address
    rw [scaling address]
    exact actualLimit address
  refine ⟨threshold, ?_⟩
  intro typical boundaryLaw retainedPaths realization convergence
  have microscopicMesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), threshold ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
          (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) /
          natural.growth^(coarse + fine + 2) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(coarse + 1) := by
    intro coarse fine edge side vertex beyond reachable
    have embeddingBound := networkEmbedding_unit_pairResistance_le (generationBlockCellEmbedding rule coarse fine edge)
      (stationaryConfiguration rule marks (coarse + fine + 1)) (plantedVertex (rule.generation fine).network side) vertex reachable
    have normalized := div_le_div_of_nonneg_right
      (embeddingBound.trans (planted_pairResistance_le_radius (rule.generation fine).network
        (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge) side vertex))
      (pow_pos (zero_lt_one.trans natural.aboveOne) (coarse + fine + 2)).le
    have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
      (stationaryConfiguration rule marks coarse edge) fine (by rw [generationEdgeAddress_length]; omega)
    rw [generationEdgeAddress_length] at cellRadius
    rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append] at normalized
    exact normalized.trans (by
      simpa only [markedElectricalRadius, stationaryConfiguration, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)
  filter_upwards [retainedPaths, convergence] with path retained converges
  let points (depth : ℕ) := actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical depth (path (depth + 1))
  have successor (depth : ℕ) (beyond : threshold ≤ depth) : dist
      (points depth) (points (depth + 1)) ≤
      ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(depth + 1) := by
    have parentLive : retainedComponentState rule marks (List.ofFn (Fin.init (path (depth + 2)))) ≠ .inactive := by
      rw [(retained (depth + 1)).1]
      exact (retained (depth + 1)).2
    have bound := actualElectricalComponentWordPoint_successor_distance rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical fieldLimit depth (path (depth + 2))
      parentLive (retained (depth + 2)).2 (((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(depth + 1))
      (fun host point reachable => microscopicMesh depth host _ _ point beyond reachable)
    simpa only [(retained (depth + 1)).1] using bound
  intro depth after
  have shifted := converges.comp (tendsto_add_atTop_nat threshold)
  have geometric := dist_le_of_le_geometric_of_tendsto eta
    (((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(threshold + 1)) etaBelowOne
    (fun index => by
      change dist (points (index + threshold)) (points (index + 1 + threshold)) ≤ _
      rw [show index + 1 + threshold = index + threshold + 1 by omega]
      have bound := successor (index + threshold) (by omega)
      simpa only [show index + threshold + 1 = index + (threshold + 1) by omega, pow_add,
        mul_assoc, mul_comm, mul_left_comm] using bound) shifted (depth - threshold)
  have ageIdentity : depth - threshold + threshold = depth := by omega
  have exponentIdentity : threshold + 1 + (depth - threshold) = depth + 1 := by omega
  change dist (points (depth - threshold + threshold)) (realization path) ≤
    ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(threshold + 1) * eta^(depth - threshold) / (1 - eta) at geometric
  rw [ageIdentity] at geometric
  calc
    _ ≤ _ := geometric
    _ = _ := by
      rw [mul_assoc, ← pow_add, exponentIdentity]
      field_simp [(sub_pos.mpr etaBelowOne).ne']

end
end IGSIII34.Spectral
