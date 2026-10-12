import IGSIII34.ResistanceLimit.ActualElectricalMassCompletion
import IGSIII34.Forms.ActualRegularityCompletion
import IGSIII34.Forms.ActualLocalityCompletion

/-! The actual full-support Perron mass, compact carrier, uniformly dense
finite-energy domain and shrinking conductive-edge mesh hold on one common
event of the original innovation law. These are constructed witnesses,
rather than an assumed Dirichlet-form record. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem exists_ae_actual_form_mass_witness_fixed_cluster
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
        ∃ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks,
        ∃ compactness : CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
          fixedPoint growth value (zero_lt_one.trans growthGreaterThanOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩))),
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
        ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
          ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value
            (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical.1.1⟩,
          weight [] marks = 1 ∧
          (∀ address, 0 ≤ weight address marks ∧
            (retainedComponentState rule marks address = .connected → 0 < weight address marks)) ∧
          IsProbabilityMeasure boundary ∧
          (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
          Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
          (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ ∧
          Dense (actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value
            (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩).carrier ∧
          (∃ threshold : ℕ, ∀ depth, threshold ≤ depth + 1 → ∀ edge,
            stationaryResistance rule p positive belowOne fixedPoint growth value marks depth edge ≤ eta ^ (depth + 1)) := by
  obtain ⟨weight, masses⟩ := exists_ae_actual_electrical_mass_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership
    eta etaPositive etaBelowOne productGreaterThanOne
  refine ⟨weight, ?_⟩
  filter_upwards [masses,
    ae_actualCompletionEnergyDomain_dense_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership
      eta etaPositive etaBelowOne productGreaterThanOne,
    ae_stationary_generation_weight_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership
      eta etaPositive etaBelowOne productGreaterThanOne] with marks mass regular mesh
  obtain ⟨electricalTypical, massCompactness, boundary, realization,
    rootWeight, positiveWeights, boundaryProbability, atoms, measurable, massProbability, openPositive,
    fullSupport, convergence, projections⟩ := mass
  obtain ⟨typical, compactness, density⟩ := regular
  refine ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, massProbability, openPositive, fullSupport, density, ?_⟩
  obtain ⟨threshold, mesh⟩ := mesh
  exact ⟨threshold, fun depth beyond edge => mesh depth beyond edge.val⟩

end
end IGSIII34.Forms
