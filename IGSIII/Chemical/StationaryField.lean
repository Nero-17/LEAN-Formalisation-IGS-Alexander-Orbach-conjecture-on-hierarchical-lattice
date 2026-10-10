import IGSIII.Chemical.TransferOrder
import IGSIII.Probability.IndependentFrontier

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability
open scoped ENNReal

noncomputable def chemicalField (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  value (innovationTreeShift rule address marks)

theorem chemicalField_measurable (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges)) :
    Measurable (chemicalField rule p positive belowOne fixedPoint value address) :=
  (Lp.stronglyMeasurable value).measurable.comp (innovationTreeShift_measurable rule address)

theorem chemicalField_positive (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks := by
  apply ae_all_iff.mpr
  intro address
  exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae valuePositive

theorem chemicalField_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    {Index : Type*} (addresses : Index → List (Fin rule.edges))
    (distinct : Function.Injective addresses) (depth : ℕ)
    (sameLength : ∀ index, (addresses index).length = depth) :
    iIndepFun (fun index => chemicalField rule p positive belowOne fixedPoint value (addresses index))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  exact (innovationFrontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    (fun _ => value) (fun _ => (Lp.stronglyMeasurable value).measurable)

theorem chemicalField_same_marginal (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (chemicalField rule p positive belowOne fixedPoint value address) =
      (independentInnovationLaw rule p positive belowOne fixedPoint).map value := by
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map (value ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (Lp.stronglyMeasurable value).measurable
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq]

theorem chemicalField_stationary_of_fixed (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (fixed : normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address,
        (edgePathFamily rule.network (marks (address, true))).shortest
          (fun edge => chemicalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
            growth * chemicalField rule p positive belowOne fixedPoint value address marks := by
  have rootIdentity : chemicalTransfer rule value =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => growth * value marks := by
    filter_upwards [Lp.coeFn_smul growth⁻¹ (chemicalTransferLp rule p positive belowOne fixedPoint 2 value),
      chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 value] with marks scalarEquality transferEquality
    have identity : growth⁻¹ * chemicalTransfer rule value marks = value marks := by
      have fixedEquality := congrArg (fun element : Lp ℝ 2
        (independentInnovationLaw rule p positive belowOne fixedPoint) => element marks) fixed
      change (growth⁻¹ • chemicalTransferLp rule p positive belowOne fixedPoint 2 value) marks = value marks at fixedEquality
      simpa only [scalarEquality, Pi.smul_apply, smul_eq_mul, transferEquality] using fixedEquality
    exact (inv_mul_eq_iff_eq_mul₀ growthPositive.ne').mp identity
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootIdentity
  filter_upwards [shifted] with marks identity
  simpa only [chemicalTransfer, chemicalField, innovationTreeShift_append, innovationTreeShift,
    List.append_nil] using identity

end IGSIII.Chemical.Substitution
