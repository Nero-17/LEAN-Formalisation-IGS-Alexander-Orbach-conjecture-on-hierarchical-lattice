import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphBirthCompletion20261011
import IGSIII34.Diffusion.FiniteCadlagSpatialMapCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.ResistanceLimit
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

abbrev actualStationaryChemicalSpaceCompletion20261011 :=
  ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence

variable [CompactSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
local instance chemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance chemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

local instance electricalChemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance electricalChemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

local instance chemicalCadlagElectricalCompletionCompactCompletion20261011 : CompactSpace
    (ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
  infer_instance

/-- The actual full-cluster CT chain placed at its canonical chemical born
vertices. These placements are not asserted to be finite-level isometries. -/
def actualPaperContinuousChemicalCadlagLawCompletion20261011
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011
      (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)) :=
  finiteContinuousCadlagProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
    (initial depth)
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩ depth)
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ depth)
    (fun vertex => actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)

include stationary fieldLimit electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds in
/-- The same true chain and exact clock give exactly the transported law;
this is a vertex-by-vertex identity, not merely an identification of masses. -/
theorem actualPaperContinuousCadlagLaw_chemical_transport_completion20261011
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) :
    (actualPaperContinuousElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive initial depth).map
      (skorokhodCadlagCarrierHomeomorphCompletion20261011
        (actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
          marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
          stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
          chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds).symm).continuous.measurable.aemeasurable =
    actualPaperContinuousChemicalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      initial depth := by
  unfold actualPaperContinuousElectricalCadlagLawCompletion20261011 actualPaperContinuousChemicalCadlagLawCompletion20261011
  rw [finiteContinuousCadlagProbability_spatial_map_completion20261011]
  congr 1
  funext vertex
  exact actualChemicalElectricalCarrierHomeomorph_symm_birth_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds depth vertex

end
end IGSIII34.Diffusion
