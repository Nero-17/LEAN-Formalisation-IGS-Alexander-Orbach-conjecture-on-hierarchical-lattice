import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphCompletion20261011
import IGSIII34.ResistanceLimit.ActualCompactness

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

/-- All electrical inputs to the actual carrier identification occur on one
proved full-measure event of the original innovation law. -/
def StationaryCarrierTypical (eta : ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : Prop :=
  StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks ∧
  (∀ address, electricalCell rule.network (marks (address, true))
    (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
      growth * electricalField rule p positive belowOne fixedPoint value address marks) ∧
  (∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address)
    atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks))) ∧
  ∃ start : ℕ, ∀ address opened depth, start ≤ address.length →
    markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1 + address.length) ≤
      ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ address.length

theorem stationaryCarrierTypical_ae_fixed_cluster
    (classicalRule : rule.Classical) (constant : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      StationaryCarrierTypical rule p positive belowOne fixedPoint growth value eta marks := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have valuePositive := electricalOmega_ae_positive rule classicalRule p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) value membership
  filter_upwards [stationaryHarmonicTypical_ae rule p positive belowOne fixedPoint growth value growthPositive valuePositive fixed,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds value fixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthGreaterThanOne growthBounds value fixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks harmonic stationary limits mesh
  exact ⟨harmonic, stationary, limits, mesh⟩

variable (growthPositive : 0 < growth) (electricalEta : ℝ)
  (electricalEtaNonnegative : 0 ≤ electricalEta) (electricalEtaBelowOne : electricalEta < 1)
  (marks : {marks // StationaryCarrierTypical rule p positive belowOne fixedPoint growth value electricalEta marks})

def carrierTypicalHarmonicMarks :
    {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks} :=
  ⟨marks.val, marks.property.1⟩

include electricalEtaNonnegative electricalEtaBelowOne in
theorem actual_carrier_homeomorph_of_typical
    (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (chemicalEta chemicalCoefficient : ℝ) (chemicalStart : ℕ)
    (chemicalEtaNonnegative : 0 ≤ chemicalEta) (chemicalEtaBelowOne : chemicalEta < 1)
    (chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient)
    (chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        chemicalCoefficient * chemicalEta ^ address.length) :
    IsHomeomorph (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1.1⟩)
      marks.property.1.1.1.2.2) := by
  obtain ⟨electricalStart, electricalBounds⟩ := marks.property.2.2.2
  exact actual_chemical_electrical_completion_homeomorph_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive (carrierTypicalHarmonicMarks rule p positive belowOne fixedPoint growth value electricalEta marks)
    classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    marks.property.2.1 marks.property.2.2.1 electricalEta ((rule.edges + 1 : ℝ) / (1 - electricalEta)) electricalStart
    electricalEtaNonnegative electricalEtaBelowOne electricalBounds chemicalEta chemicalCoefficient chemicalStart
    chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds

end
end IGSIII34.ResistanceLimit
