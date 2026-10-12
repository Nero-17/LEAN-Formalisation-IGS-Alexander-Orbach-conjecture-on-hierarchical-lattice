import IGSIII34.Diffusion.ElectricalDegreeConvergenceCompletion
import IGSIII34.ResistanceLimit.ActualElectricalMassCompletion

/-! The full-support electrical speed measure comes from the same actual
Perron cylinder law as Section 2. Field convergence and both mesh events used
in this construction were proved on the original innovation probability law.
The measure is constructed on the electrical metric completion. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem exists_ae_actual_degree_electrical_mass_fixed_cluster_completion
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
          Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
          (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ ∧
          (∀ᵐ path ∂boundary, Tendsto (fun depth => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
            growth value (zero_lt_one.trans growthGreaterThanOne) marks typical depth (path (depth + 1)))
              atTop (𝓝 (realization path))) ∧
          Tendsto (fun depth => levyProkhorovEDist
            (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value
              (zero_lt_one.trans growthGreaterThanOne) marks typical depth (path (depth + 1))))
            (boundary.map realization)) atTop (𝓝 0) ∧
          ∀ chemicalScale : ℝ, ∀ chemicalScalePositive : 0 < chemicalScale,
            Tendsto (fun depth => levyProkhorovEDist
              (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value
                (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ chemicalScale chemicalScalePositive depth)
              (boundary.map realization)) atTop (𝓝 0) := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have valuePositive := electricalOmega_ae_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) value membership
  obtain ⟨weight, massProperties⟩ := actual_component_boundary_probability_law classicalRule p positive belowOne fixedPoint
  obtain ⟨jointWeight, jointProperties⟩ := actual_component_joint_edge_vertex_weights classicalRule p positive belowOne fixedPoint
  refine ⟨weight, ?_⟩
  filter_upwards [massProperties,
    stationaryElectricalTypical_ae rule p positive belowOne fixedPoint growth value growthPositive valuePositive valueFixed,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds value valueFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthGreaterThanOne growthBounds value valueFixed membership eta etaPositive etaBelowOne productGreaterThanOne,
    jointProperties,
    IGSIII34.Forms.ae_stationary_generation_weight_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership eta etaPositive etaBelowOne
      productGreaterThanOne] with marks masses typical fields radiusMesh joint weightMesh
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
  have sameWeight (address : List (Fin rule.edges × Bool)) : jointWeight address marks = weight address marks := by
    have firstLimit := (joint.2.1 address).2.1
    have secondLimit := (masses.2.1 address).2.2.1
    change Tendsto (fun depth => markedComponentVertexMass rule marks depth address /
      markedComponentVertexMass rule marks (depth + address.length) []) atTop (𝓝 (weight address marks)) at secondLimit
    exact tendsto_nhds_unique firstLimit secondLimit
  have edgeLimits (age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) : Tendsto
      (fun fine => edgeComponentWordWeight rule marks fine age word) atTop (𝓝 (weight (List.ofFn word) marks)) := by
    have converges := (joint.2.1 (List.ofFn word)).2.2
    rw [sameWeight] at converges
    simpa only [edgeComponentWordWeight, List.length_ofFn] using converges
  refine ⟨typical, compactness, boundary, realization, masses.1,
    (fun address => ⟨(masses.2.1 address).1, (masses.2.1 address).2.2.2.2⟩), probability, atoms,
    measurable, pushProbability, openPositive, support, convergence, projection, ?_⟩
  intro chemicalScale chemicalScalePositive
  exact actualElectrical_degree_mass_tendsto_completion rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks, typical⟩ fields eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
    chemicalScale chemicalScalePositive (fun address => weight address marks) (fun address => (masses.2.1 address).1)
    boundary atoms edgeLimits realization projection

end
end IGSIII34.Diffusion
