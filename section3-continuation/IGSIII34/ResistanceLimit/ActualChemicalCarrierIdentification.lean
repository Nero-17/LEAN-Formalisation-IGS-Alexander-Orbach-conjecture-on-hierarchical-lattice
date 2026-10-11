import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphAE
import IGSIII.Geometry.CriticalChemicalLengths
import IGSIII34.ResistanceLimit.ActualChemicalCommonRealisationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)

/-- Identification with the actual chemical carrier of Section 2. Every
chemical length, convergence and mesh input is supplied by the model, rather
than imposed on an arbitrary metric completion. -/
def ActualChemicalCarrierIdentification : Prop :=
  ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ chemicalGrowth ∧
    chemicalGrowth ≤ longestTerminalPath rule.network ∧
    ∃ amplitude : ℝ, 1 ≤ amplitude ∧
    ∃ chemicalValue : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks,
        ∃ lengthNonnegative : ∀ depth edge, 0 ≤
          chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks depth edge,
        ∃ lengthPositive : ∀ depth edge, stationaryConfiguration rule marks depth edge = true → 0 <
          chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks depth edge,
        ∃ childConvergence : ∀ coarse edge, Tendsto (fun fine =>
          (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
            (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).dist
            (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
            chemicalGrowth ^ (coarse + fine + 2)) atTop
          (𝓝 (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks coarse edge)),
        IsHomeomorph (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule
          (stationaryConfiguration rule marks)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks,typical.1.1⟩)
          chemicalGrowth chemicalGrowthPositive
          (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
          lengthNonnegative lengthPositive childConvergence
          (stationaryResistance rule p positive belowOne fixedPoint growth value marks)
          (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks,typical.1.1⟩)
          typical.1.1.2.2) ∧
        ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
          letI := ambientMetric
          CompleteSpace Ambient ∧ CompactSpace Ambient ∧
          ∃ target : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks)
            (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks,typical.1.1⟩)
            chemicalGrowth chemicalGrowthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
            lengthNonnegative lengthPositive childConvergence → Ambient,
            Isometry target ∧
          ∃ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks)
            chemicalGrowth chemicalGrowthPositive depth → Ambient,
            (∀ depth, Isometry (sources depth)) ∧
            ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
              dist (sources depth point) (target (actualChemicalVertex rule classicalRule
                (stationaryConfiguration rule marks)
                (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks,typical.1.1⟩)
                chemicalGrowth chemicalGrowthPositive
                (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
                lengthNonnegative lengthPositive childConvergence depth point)) < tolerance

theorem actual_chemical_carrier_identification_fixed_cluster
    (constant : ℝ) (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ActualChemicalCarrierIdentification rule classicalRule p positive belowOne fixedPoint growth value growthPositive := by
  obtain ⟨chemicalConstant, chemicalGrowth, _, _, chemicalGrowthLower, chemicalGrowthUpper, meanBounds,
    chemicalValue, _, _, _, amplitude, amplitudeAtLeastOne, fieldLimits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have chemicalGrowthGreaterThanOne : 1 < chemicalGrowth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le chemicalGrowthLower
  have chemicalGrowthPositive := zero_lt_one.trans chemicalGrowthGreaterThanOne
  let chemicalEta : ℝ := (chemicalGrowth + 1) / (2 * chemicalGrowth)
  have chemicalEtaPositive : 0 < chemicalEta := div_pos (by linarith) (by positivity)
  have chemicalEtaBelowOne : chemicalEta < 1 :=
    (div_lt_one (by positivity : 0 < 2 * chemicalGrowth)).mpr (by linarith)
  have chemicalProductGreaterThanOne : 1 < chemicalGrowth * chemicalEta := by
    have identity : chemicalGrowth * chemicalEta = (chemicalGrowth + 1) / 2 := by
      dsimp [chemicalEta]
      field_simp
    rw [identity]
    linarith
  let electricalEta : ℝ := (growth + 1) / (2 * growth)
  have electricalEtaPositive : 0 < electricalEta := div_pos (by linarith) (by positivity)
  have electricalEtaBelowOne : electricalEta < 1 :=
    (div_lt_one (by positivity : 0 < 2 * growth)).mpr (by linarith)
  have electricalProductGreaterThanOne : 1 < growth * electricalEta := by
    have identity : growth * electricalEta = (growth + 1) / 2 := by
      dsimp [electricalEta]
      field_simp
    rw [identity]
    linarith
  refine ⟨chemicalGrowth, chemicalGrowthPositive, chemicalGrowthLower, chemicalGrowthUpper,
    amplitude, amplitudeAtLeastOne, chemicalValue, ?_⟩
  filter_upwards [stationaryCarrierTypical_ae_fixed_cluster rule p positive belowOne fixedPoint growth value
      classicalRule constant constantPositive growthGreaterThanOne growthBounds fixed membership
      electricalEta electricalEtaPositive electricalEtaBelowOne electricalProductGreaterThanOne,
    fieldLimits,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint chemicalConstant
      chemicalGrowth chemicalGrowthPositive meanBounds chemicalEta chemicalEtaPositive chemicalEtaBelowOne chemicalProductGreaterThanOne]
    with marks electrical fields chemicalMesh
  obtain ⟨lengthNonnegative, lengthPositive, childConvergence⟩ := actual_block_lengths_of_terminal_field
    rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalGrowthPositive
    (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks electrical.1.1.1.2.1
    (fun address => (fields address).1) (fun address => (fields address).2.2)
  obtain ⟨chemicalStart, chemicalBounds⟩ := chemicalMesh
  refine ⟨electrical.1, lengthNonnegative, lengthPositive, childConvergence, ?_, ?_⟩
  · exact actual_carrier_homeomorph_of_typical rule p positive belowOne fixedPoint growth value growthPositive
      electricalEta electricalEtaPositive.le electricalEtaBelowOne ⟨marks,electrical⟩ classicalRule
      chemicalGrowth chemicalGrowthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
      lengthNonnegative lengthPositive childConvergence chemicalEta ((rule.edges + 1 : ℝ) / (1 - chemicalEta)) chemicalStart
      chemicalEtaPositive.le chemicalEtaBelowOne
      (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le) chemicalBounds
  · exact exists_actual_chemical_common_isometric_realisation_completion20261011 rule classicalRule marks
      electrical.1.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks,electrical.1.1.1⟩)
      chemicalGrowth chemicalGrowthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
      lengthNonnegative lengthPositive childConvergence chemicalEta ((rule.edges + 1 : ℝ) / (1 - chemicalEta)) chemicalStart
      chemicalEtaPositive.le chemicalEtaBelowOne
      (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le) chemicalBounds

end
end IGSIII34.ResistanceLimit
