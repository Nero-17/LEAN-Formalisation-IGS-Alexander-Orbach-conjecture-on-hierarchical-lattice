import IGSIII.Geometry.CellLocalisationAddressCompletion
import IGSIII.Geometry.CellLocalisationShiftData
import IGSIII.Geometry.CellLocalisationConfigurationSimilarity

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory Filter
open scoped Topology ENNReal

variable (rule : Rule) (classicalRule : rule.Classical)
variable (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (coherent : ∀ address opened, configurationSequenceCoherent rule
  (fun depth => markedGenerationConfiguration rule marks depth address opened))
variable (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
variable (fieldConvergence : ∀ address, Tendsto
  (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
  atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))

/-- Every actual intrinsic descendant completion is a canonical similarity
copy of the completed root model on its actual shifted C/N innovation tree. -/
def chemicalShiftedRootToAddressSimilarity (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ) :
    ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value (innovationTreeShift rule address marks) (innovationTreeShift_crossing rule marks crossing address) (innovationTreeShift_coherent rule marks coherent address) (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive address) (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence address) [] opened sourceSide 0 ≃ᵤ
      ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset := by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value (innovationTreeShift rule address marks) (innovationTreeShift_crossing rule marks crossing address)
    (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive address)
    (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence address) [] opened 0
  let lastData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened offset
  exact rootedComponentCompletionSimilarityOfConfiguration rule classicalRule
    (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth [] opened)
    (fun depth => markedGenerationConfiguration rule marks depth address opened)
    ((innovationTreeShift_coherent rule marks coherent address) [] opened) (coherent address opened) sourceSide growth growthPositive 0 offset
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value (innovationTreeShift rule address marks) [] opened 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset)
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2
    (funext (fun depth => by simpa only [List.append_nil] using markedGenerationConfiguration_shift rule marks address depth [] opened))
    (growth ^ offset)⁻¹ (inv_pos.mpr (pow_pos growthPositive offset))
    (chemicalAddressBlockLimitLength_shift_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks address opened offset)

theorem chemicalShiftedRootToAddressSimilarity_distance (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ)
    (first last : ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value (innovationTreeShift rule address marks) (innovationTreeShift_crossing rule marks crossing address) (innovationTreeShift_coherent rule marks coherent address) (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive address) (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence address) [] opened sourceSide 0) :
    dist (chemicalShiftedRootToAddressSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset first)
      (chemicalShiftedRootToAddressSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset last) =
      (growth ^ offset)⁻¹ * dist first last := by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value (innovationTreeShift rule address marks) (innovationTreeShift_crossing rule marks crossing address)
    (innovationTreeShift_field_positive rule p positive belowOne fixedPoint value marks fieldPositive address)
    (innovationTreeShift_field_convergence rule p positive belowOne fixedPoint growth amplitude value marks fieldConvergence address) [] opened 0
  let lastData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened offset
  exact rootedComponentCompletionSimilarityOfConfiguration_distance rule classicalRule
    (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth [] opened)
    (fun depth => markedGenerationConfiguration rule marks depth address opened)
    ((innovationTreeShift_coherent rule marks coherent address) [] opened) (coherent address opened) sourceSide growth growthPositive 0 offset
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value (innovationTreeShift rule address marks) [] opened 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset)
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2
    (funext (fun depth => by simpa only [List.append_nil] using markedGenerationConfiguration_shift rule marks address depth [] opened))
    (growth ^ offset)⁻¹ (inv_pos.mpr (pow_pos growthPositive offset))
    (chemicalAddressBlockLimitLength_shift_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks address opened offset) first last

end
end IGSIII.Geometry
