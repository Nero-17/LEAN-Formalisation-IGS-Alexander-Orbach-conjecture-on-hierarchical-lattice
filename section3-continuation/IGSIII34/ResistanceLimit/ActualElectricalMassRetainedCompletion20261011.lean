import IGSIII34.ResistanceLimit.ActualElectricalMassCompletion20261011
import IGSIII34.ResistanceLimit.ElectricalMassCompletion20261011

/-! The full-support electrical speed measure comes from the same actual
Perron cylinder law as Section 2. Field convergence and both mesh events used
in this construction were proved on the original innovation probability law.
This does not yet identify the electrical and chemical completions. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem exists_ae_actual_electrical_mass_retained_fixed_cluster_completion20261011
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address, Tendsto (fun depth =>
          markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
          atTop (𝓝 (weight address marks))) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ typical : StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks,
        ∃ compactness : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value
          (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩),
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
        ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
          ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value
            (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩,
          weight [] marks = 1 ∧
          (∀ address, 0 ≤ weight address marks ∧
            (retainedComponentState rule marks address = .connected → 0 < weight address marks)) ∧
          IsProbabilityMeasure boundary ∧
          (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
          (∀ᵐ path ∂boundary, ∀ depth,
            Fin.init (path (depth + 1)) = path depth ∧
              retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive) ∧
          Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
          (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ ∧
          (∀ᵐ path ∂boundary, Tendsto (fun depth => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
            growth value (zero_lt_one.trans growthGreaterThanOne) marks typical depth (path (depth + 1)))
              atTop (𝓝 (realization path))) ∧
          Tendsto (fun depth => levyProkhorovEDist
            (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value
              (zero_lt_one.trans growthGreaterThanOne) marks typical depth (path (depth + 1))))
            (boundary.map realization)) atTop (𝓝 0) := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have valuePositive := electricalOmega_ae_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) value membership
  obtain ⟨weight, massProperties⟩ := actual_component_boundary_probability_law classicalRule p positive belowOne fixedPoint
  refine ⟨weight, ?_, ?_⟩
  · filter_upwards [massProperties] with marks masses
    exact fun address => (masses.2.1 address).2.2.1
  filter_upwards [massProperties,
    stationaryElectricalTypical_ae rule p positive belowOne fixedPoint growth value growthPositive valuePositive valueFixed,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds value valueFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthGreaterThanOne growthBounds value valueFixed membership eta etaPositive etaBelowOne productGreaterThanOne,
    IGSIII34.Forms.ae_stationary_generation_weight_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership eta etaPositive etaBelowOne
      productGreaterThanOne] with marks masses typical fields radiusMesh weightMesh
  obtain ⟨start, radiusBounds⟩ := radiusMesh
  obtain ⟨weightStart, weightBounds⟩ := weightMesh
  have coefficientNonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le
  have compactness := actualStationaryElectricalSpace_compact rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks, typical⟩ fields eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    coefficientNonnegative radiusBounds
  obtain ⟨boundary, probability, atoms, retained⟩ := masses.2.2
  letI := probability
  have microscopicMesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
          (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) /
          growth ^ (coarse + fine + 2) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (coarse + 1) := by
    intro coarse fine edge side vertex beyond reachable
    have embeddingBound := networkEmbedding_unit_pairResistance_le (generationBlockCellEmbedding rule coarse fine edge)
      (stationaryConfiguration rule marks (coarse + fine + 1)) (plantedVertex (rule.generation fine).network side) vertex reachable
    have normalized := div_le_div_of_nonneg_right
      (embeddingBound.trans (planted_pairResistance_le_radius (rule.generation fine).network
        (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge) side vertex))
      (pow_pos growthPositive (coarse + fine + 2)).le
    have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
      (stationaryConfiguration rule marks coarse edge) fine (by rw [generationEdgeAddress_length]; omega)
    rw [generationEdgeAddress_length] at cellRadius
    rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append] at normalized
    exact normalized.trans (by
      simpa only [markedElectricalRadius, stationaryConfiguration, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)
  obtain ⟨realization, measurable, pushProbability, openPositive, support, convergence, projection⟩ :=
    exists_actual_electrical_boundary_full_support rule p positive belowOne fixedPoint growth value growthPositive
      marks typical fields boundary (by
        filter_upwards [retained] with path properties
        exact fun depth => ⟨(properties depth).1, (properties depth).2.2.1⟩)
      (fun address => weight address marks) atoms (fun address => (masses.2.1 address).2.2.2.2)
      eta ((rule.edges + 1 : ℝ) / (1 - eta)) etaPositive.le etaBelowOne coefficientNonnegative start microscopicMesh
      weightStart (fun depth after edge => weightBounds depth (after.trans (Nat.le_succ depth)) edge.val)
  exact ⟨typical, compactness, boundary, realization, masses.1,
    (fun address => ⟨(masses.2.1 address).1, (masses.2.1 address).2.2.2.2⟩), probability, atoms,
    (by
      filter_upwards [retained] with path properties
      exact fun depth => ⟨(properties depth).1, (properties depth).2.2.1⟩),
    measurable, pushProbability, openPositive, support, convergence, projection⟩

end
end IGSIII34.ResistanceLimit
