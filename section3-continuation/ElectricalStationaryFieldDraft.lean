import IGSIII34.Percolation.ElectricalNormalization
import IGSIII.Probability.IndependentFrontier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

noncomputable def electricalField (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  value (innovationTreeShift rule address marks)

theorem electricalField_measurable (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges)) :
    Measurable (electricalField rule p positive belowOne fixedPoint value address) :=
  (Lp.stronglyMeasurable value).measurable.comp (innovationTreeShift_measurable rule address)

theorem electricalField_positive (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 < electricalField rule p positive belowOne fixedPoint value address marks := by
  apply ae_all_iff.mpr
  intro address
  exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae valuePositive

theorem electricalField_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    {Index : Type*} (addresses : Index → List (Fin rule.edges))
    (distinct : Function.Injective addresses) (depth : ℕ)
    (sameLength : ∀ index, (addresses index).length = depth) :
    iIndepFun (fun index => electricalField rule p positive belowOne fixedPoint value (addresses index))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  exact (innovationFrontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    (fun _ => value) (fun _ => (Lp.stronglyMeasurable value).measurable)

theorem electricalField_same_marginal (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (electricalField rule p positive belowOne fixedPoint value address) =
      (independentInnovationLaw rule p positive belowOne fixedPoint).map value := by
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map (value ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (Lp.stronglyMeasurable value).measurable
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq]

theorem electricalField_stationary_of_fixed (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address,
        electricalCell rule.network (marks (address, true))
          (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
            growth * electricalField rule p positive belowOne fixedPoint value address marks := by
  have rootIdentity : nonnegativeElectricalTransfer rule value =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => growth * value marks := by
    filter_upwards [Lp.coeFn_smul growth⁻¹ (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint 2 value),
      nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 value] with marks scalarEquality transferEquality
    have identity : growth⁻¹ * nonnegativeElectricalTransfer rule value marks = value marks := by
      have fixedEquality := congrArg (fun element : Lp ℝ 2
        (independentInnovationLaw rule p positive belowOne fixedPoint) => element marks) fixed
      change (growth⁻¹ • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint 2 value) marks = value marks at fixedEquality
      simpa only [scalarEquality, Pi.smul_apply, smul_eq_mul, transferEquality] using fixedEquality
    exact (inv_mul_eq_iff_eq_mul₀ growthPositive.ne').mp identity
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootIdentity
  filter_upwards [shifted, electricalField_positive rule p positive belowOne fixedPoint value valuePositive]
    with marks identity fieldPositive
  have translated : electricalCell rule.network (marks (address, true))
      (fun edge => max (electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) 0) =
        growth*electricalField rule p positive belowOne fixedPoint value address marks := by
    simpa only [nonnegativeElectricalTransfer, electricalTransfer, electricalField,
      innovationTreeShift_append, innovationTreeShift, List.append_nil] using identity
  have clipping (edge : Fin rule.edges) :
      max (electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) 0 =
        electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks :=
    max_eq_left (fieldPositive (address ++ [edge])).le
  simpa only [clipping] using translated


end
end IGSIII34.Percolation
