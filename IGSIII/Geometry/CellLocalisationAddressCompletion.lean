import IGSIII.Geometry.CellLocalisationAddressScaling
import IGSIII.Geometry.CellLocalisationScaledCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
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

/-- The actual intrinsic completion at any address, crossing state and planted
side, with its explicitly derived child lengths and global scale offset. -/
def ChemicalAddressRootedSpace (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ) : Type :=
  let componentData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened offset
  RootedComponentSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth address opened)
    (coherent address opened) sourceSide growth growthPositive offset
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset)
    componentData.1 componentData.2.1 componentData.2.2

instance chemicalAddressRootedSpaceMetricSpace (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ) :
    MetricSpace (ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset) := by
  unfold ChemicalAddressRootedSpace
  infer_instance

/-- The complete intrinsic cell is a similarity copy of its zero-offset
rooted completion with the exact factor given by its global depth. -/
def chemicalAddressRootedSpaceSimilarity (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ) :
    ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide 0 ≃ᵤ
      ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset := by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened 0
  let lastData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened offset
  exact rootedComponentCompletionSimilarity rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth address opened) (coherent address opened) sourceSide growth growthPositive 0 offset
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset)
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2 (growth ^ offset)⁻¹
    (inv_pos.mpr (pow_pos growthPositive offset))
    (chemicalAddressBlockLimitLength_offset_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks address opened offset)

theorem chemicalAddressRootedSpaceSimilarity_distance (address : List (Fin rule.edges)) (opened sourceSide : Bool) (offset : ℕ)
    (first last : ChemicalAddressRootedSpace rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide 0) :
    dist (chemicalAddressRootedSpaceSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset first)
      (chemicalAddressRootedSpaceSimilarity rule classicalRule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing coherent fieldPositive fieldConvergence address opened sourceSide offset last) =
      (growth ^ offset)⁻¹ * dist first last :=
by
  let firstData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened 0
  let lastData := address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence address opened offset
  exact rootedComponentCompletionSimilarity_distance rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth address opened) (coherent address opened) sourceSide growth growthPositive 0 offset
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened 0)
    (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset)
    firstData.1 firstData.2.1 lastData.1 lastData.2.1 firstData.2.2 lastData.2.2 (growth ^ offset)⁻¹
    (inv_pos.mpr (pow_pos growthPositive offset))
    (chemicalAddressBlockLimitLength_offset_scale rule p positive belowOne fixedPoint growth amplitude growthPositive value marks address opened offset) first last

end
end IGSIII.Geometry


