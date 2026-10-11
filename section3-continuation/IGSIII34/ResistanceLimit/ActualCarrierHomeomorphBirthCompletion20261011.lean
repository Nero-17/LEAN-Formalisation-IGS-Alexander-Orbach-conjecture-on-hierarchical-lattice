import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

variable (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

variable
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (electricalEta electricalCoefficient : ℝ) (electricalStart : ℕ)
    (electricalEtaNonnegative : 0 ≤ electricalEta) (electricalEtaBelowOne : electricalEta < 1)
    (electricalRadiusBounds : ∀ address opened depth, electricalStart ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        electricalCoefficient * electricalEta ^ address.length)
    (chemicalEta chemicalCoefficient : ℝ) (chemicalStart : ℕ)
    (chemicalEtaNonnegative : 0 ≤ chemicalEta) (chemicalEtaBelowOne : chemicalEta < 1)
    (chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient)
    (chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        chemicalCoefficient * chemicalEta ^ address.length)
def actualChemicalElectricalCarrierHomeomorphCompletion20261011 :=
  IsHomeomorph.homeomorph _
    (actual_chemical_electrical_completion_homeomorph_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
      chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds)

theorem actualChemicalElectricalCarrierHomeomorph_birth_completion20261011
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
      chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
      (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex) =
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex := by
  exact chemicalElectricalCompletionMap_birth_completion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2
    (actualChemicalElectricalSkeletonMap_uniformContinuous_completion20261011 rule classicalRule p positive belowOne
      fixedPoint growth growthPositive value ⟨marks.val,marks.property.1.1⟩ fieldLimit chemicalScale chemicalScalePositive lengths
      lengthNonnegative lengthPositive childConvergence electricalEta electricalCoefficient electricalStart electricalEtaNonnegative
      electricalEtaBelowOne electricalRadiusBounds) depth vertex

theorem actualChemicalElectricalCarrierHomeomorph_symm_birth_completion20261011
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    (actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
      chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds).symm
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex) =
      actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex := by
  rw [← actualChemicalElectricalCarrierHomeomorph_birth_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds depth vertex]
  exact Homeomorph.symm_apply_apply _ _

end
end IGSIII34.ResistanceLimit