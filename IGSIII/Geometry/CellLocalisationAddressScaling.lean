import IGSIII.Geometry.CellLocalisationMetricCode
import IGSIII.Geometry.GenericComponentLengths

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory

/-- Descendant extraction uses the exact same raw C/N marks as the tree shift. -/
theorem markedGenerationConfiguration_shift (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (depth : ℕ) (suffix : List (Fin rule.edges)) (opened : Bool) :
    markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth suffix opened =
      markedGenerationConfiguration rule marks depth (address ++ suffix) opened := by
  induction depth generalizing suffix opened with
  | zero => rfl
  | succ depth inductionHypothesis =>
    simp only [markedGenerationConfiguration, inductionHypothesis, innovationTreeShift, List.append_assoc]

/-- A descendant's global-units leaf lengths are its shifted root lengths
multiplied by precisely the inverse growth factor of its depth. -/
theorem chemicalAddressBlockLimitLength_shift_scale (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth amplitude : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened : Bool) (offset coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
    chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset coarse edge =
      (growth ^ offset)⁻¹ * chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value
        (innovationTreeShift rule address marks) [] opened 0 coarse edge := by
  classical
  unfold chemicalAddressBlockLimitLength
  rw [markedGenerationConfiguration_shift]
  simp only [List.append_nil, List.nil_append, Nat.add_zero]
  split_ifs
  · rw [chemicalField_shift, pow_add]
    field_simp
  · simp only [mul_zero]

theorem chemicalAddressBlockLimitLength_offset_scale (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth amplitude : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened : Bool) (offset coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
    chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset coarse edge =
      (growth ^ offset)⁻¹ * chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value
        marks address opened 0 coarse edge := by
  classical
  unfold chemicalAddressBlockLimitLength
  simp only [Nat.add_zero]
  split_ifs
  · rw [pow_add]
    field_simp
  · simp only [mul_zero]

end
end IGSIII.Geometry
