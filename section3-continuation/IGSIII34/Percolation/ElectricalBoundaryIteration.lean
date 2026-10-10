import IGSIII34.Percolation.ElectricalWeightedGeneration
import IGSIII34.Percolation.ElectricalTransferBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
variable {Sample : Type*} [MeasurableSpace Sample]

def positiveRepresentative (value : Sample → ℝ) : Sample → ℝ :=
  fun sample => if 0 < value sample then value sample else 1

theorem positiveRepresentative_positive (value : Sample → ℝ) (sample : Sample) : 0 < positiveRepresentative value sample := by
  unfold positiveRepresentative
  split_ifs with positive
  · exact positive
  · exact zero_lt_one

theorem positiveRepresentative_measurable {value : Sample → ℝ} (measurable : Measurable value) :
    Measurable (positiveRepresentative value) :=
  measurable.ite (measurableSet_lt measurable_const measurable) measurable_const

theorem positiveRepresentative_ae_eq {value : Sample → ℝ} (measure : Measure Sample)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample) : positiveRepresentative value =ᵐ[measure] value := by
  filter_upwards [positive] with sample positive
  exact if_pos positive

end
end IGSIII34.Probability
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem electricalTransfer_iterate_nonnegative (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (nonnegative : ∀ marks, 0 ≤ value marks) (depth : ℕ) :
    ∀ marks, 0 ≤ (electricalTransfer rule)^[depth] value marks := by
  induction depth with
  | zero => exact nonnegative
  | succ depth previous =>
      rw [Function.iterate_succ_apply']
      exact electricalTransfer_nonnegative rule _ previous

theorem nonnegativeElectricalTransferLp_iterate_positive_representative_ae (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) (depth : ℕ) :
    ⇑((nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint 2)^[depth] value) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      (electricalTransfer rule)^[depth] (positiveRepresentative value) := by
  induction depth with
  | zero => exact (positiveRepresentative_ae_eq _ valuePositive).symm
  | succ depth previous =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have congruent := nonnegativeElectricalTransfer_congr_ae rule p positive belowOne fixedPoint previous
      have clipping : (fun marks => max (((electricalTransfer rule)^[depth] (positiveRepresentative value)) marks) 0) =
          (electricalTransfer rule)^[depth] (positiveRepresentative value) :=
        funext (fun marks => max_eq_left (electricalTransfer_iterate_nonnegative rule _
          (fun sample => (positiveRepresentative_positive value sample).le) depth marks))
      filter_upwards [nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 _, congruent]
        with marks equality congruence
      rw [equality, congruence, nonnegativeElectricalTransfer, clipping]

theorem normalizedElectricalTransferLp_iterate_weighted_actual_ae (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) (depth : ℕ) :
    ⇑((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] value) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => (growth⁻¹)^(depth+1)*electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
        (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
  rw [normalizedElectricalTransferLp_iterate rule p positive belowOne fixedPoint 2 growth growthNonnegative]
  filter_upwards [Lp.coeFn_smul ((growth⁻¹)^(depth+1))
      ((nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint 2)^[depth+1] value),
    nonnegativeElectricalTransferLp_iterate_positive_representative_ae rule p positive belowOne fixedPoint value valuePositive (depth+1),
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks scalarEquality iterationEquality crossing
  rw [scalarEquality, Pi.smul_apply, smul_eq_mul, iterationEquality]
  congr 1
  have rootShift : innovationTreeShift rule [] marks = marks := by funext coordinate; rfl
  have weighted := electricalTransfer_iterate_eq_weighted_actual rule (positiveRepresentative value) marks crossing
    (fun address => positiveRepresentative_positive value _) depth []
  simpa only [rootShift, List.nil_append] using weighted

end
end IGSIII34.Percolation
