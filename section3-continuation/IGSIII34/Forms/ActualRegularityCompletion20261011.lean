import IGSIII34.Forms.CompletionRegularityCompletion20261011
import IGSIII34.Forms.ActualEnergyHilbert
import IGSIII34.ResistanceLimit.ActualResistanceAttainment
import IGSIII34.ResistanceLimit.ActualCompactness

/-! Regularity for the full retained stationary electrical completion. All
finite trace and separation inputs are the already proved actual-model facts.
Compactness is the independently proved actual full-mesh conclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

def actualCompletionEnergyDomain :=
  completionEnergyDomain
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))

theorem actualCompletionEnergyDomain_separates
    (first last : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))
    (distinct : first ≠ last) :
    ∃ potential ∈ actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks,
      potential first ≠ potential last :=
  completionEnergyDomain_separates
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_skeleton_resistance_attained rule p positive belowOne fixedPoint growth value growthPositive marks)

    first last distinct

theorem actualCompletionEnergyDomain_dense
    [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))] :
    Dense (actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks).carrier := by
  letI : CompactSpace (UniformSpace.Completion
      (ElectricalSkeleton rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2)) :=
    inferInstanceAs (CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))))
  exact completionEnergyDomain_dense
    (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_skeleton_resistance_attained rule p positive belowOne fixedPoint growth value growthPositive marks)

theorem ae_actualCompletionEnergyDomain_dense_fixed_cluster
    (rule : Rule) (classical : rule.Classical)
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
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks,
        CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
          fixedPoint growth value (zero_lt_one.trans growthGreaterThanOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩))) ∧
        Dense (actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value
          (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩).carrier := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have valuePositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) value membership
  filter_upwards [stationaryHarmonicTypical_ae rule p positive belowOne fixedPoint growth value growthPositive
      valuePositive valueFixed,
    ae_actualStationaryElectricalSpace_compact_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds value valueFixed membership eta etaPositive
      etaBelowOne productGreaterThanOne] with marks typical compact
  obtain ⟨electricalTypical, compact⟩ := compact
  letI : CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩))) := compact
  exact ⟨typical, inferInstance,
    actualCompletionEnergyDomain_dense rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩⟩

end
end IGSIII34.Forms
