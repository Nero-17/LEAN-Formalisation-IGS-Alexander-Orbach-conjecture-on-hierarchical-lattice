import IGSIII34.Percolation.ElectricalWeightedGeneration
import IGSIII34.Percolation.ElectricalStationaryField
import IGSIII34.ResistanceLimit.StationaryGeneration

/-! Exact all-depth electrical response of the actual stationary field.
This is an algebraic consequence of the one-step fixed-field identity and
actual graph substitution, rather than an additional scale-compatibility
assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

theorem stationary_field_block_response
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    electricalCell (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth address true)
      (fun leaf => field (address ++ generationEdgeAddress rule depth leaf)) =
      growth ^ (depth + 1) * field address := by
  induction depth generalizing address with
  | zero =>
      simpa only [Rule.generation, generationEdgeAddress, markedGenerationConfiguration,
        List.append_nil, Nat.zero_add, pow_one] using stationary address
  | succ depth previous =>
      rw [generation_weighted_resistance_recursion rule depth _
        (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) address true)
        _ (fun leaf => fieldPositive _),
        markedGenerationConfiguration_root rule marks crossing,
        markedGenerationConfiguration_topCells]
      have onOpen (edge : Fin rule.edges) (retained : marks (address, true) edge = true) :
          electricalCell (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, true) edge))
            (fun child => field (address ++ generationEdgeAddress rule (depth + 1)
              ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))))) =
          growth ^ (depth + 1) * field (address ++ [edge]) := by
        rw [retained]
        convert previous (address ++ [edge]) using 1
        congr 1
        funext child
        rw [generationEdgeAddress_top]
        simp only [List.append_assoc, List.singleton_append]
      rw [electricalCell_depends_open rule.network (marks (address, true)) _ _ onOpen,
        electricalCell_scale rule.network (marks (address, true))
          (fun edge => (fieldPositive _).le) (pow_pos growthPositive _).le,
        stationary address, pow_succ]
      ring

theorem stationary_field_normalized_block_response
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    electricalCell (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth address true)
      (fun leaf => stationaryGenerationResistance rule field growth depth address leaf) = field address := by
  unfold stationaryGenerationResistance
  rw [electricalCell_scale (rule.generation depth).network _
    (fun leaf => (fieldPositive _).le) (pow_pos (inv_pos.mpr growthPositive) _).le,
    stationary_field_block_response rule marks field growth growthPositive fieldPositive crossing stationary]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ growthPositive.ne', one_pow, one_mul]

theorem actual_stationary_block_response_ae
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ depth address,
        electricalCell (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address true)
          (fun leaf => stationaryGenerationResistance rule
            (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
            growth depth address leaf) =
          electricalField rule p positive belowOne fixedPoint value address marks := by
  filter_upwards [electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks fieldPositive stationary crossing
  exact fun depth address => stationary_field_normalized_block_response rule marks
    (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
    growth growthPositive fieldPositive crossing stationary depth address

end
end IGSIII34.ResistanceLimit
