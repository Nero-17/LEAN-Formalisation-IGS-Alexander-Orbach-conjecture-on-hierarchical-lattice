import IGSIII34.Percolation.ElectricalLp
import IGSIII.Chemical.TransferOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped ENNReal

theorem nonnegativeElectricalTransfer_congr_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (equal : first =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint] second) :
    nonnegativeElectricalTransfer rule first =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      nonnegativeElectricalTransfer rule second := by
  have coordinates : ∀ edge : Fin rule.edges,
      (fun marks => first (innovationTreeShift rule [edge] marks)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => second (innovationTreeShift rule [edge] marks)) :=
    fun edge => (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae_eq_comp equal
  filter_upwards [ae_all_iff.mpr coordinates] with marks equality
  unfold nonnegativeElectricalTransfer electricalTransfer
  congr 1
  funext edge
  exact congrArg (fun value : ℝ => max value 0) (equality edge)

theorem nonnegativeElectricalTransfer_mono_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (comparison : first ≤ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint] second) :
    nonnegativeElectricalTransfer rule first ≤ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      nonnegativeElectricalTransfer rule second := by
  have coordinates : ∀ edge : Fin rule.edges,
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        first (innovationTreeShift rule [edge] marks) ≤ second (innovationTreeShift rule [edge] marks) :=
    fun edge => (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae comparison
  filter_upwards [ae_all_iff.mpr coordinates] with marks inequalities
  exact electricalCell_monotone rule.network (marks ([], true))
    (fun _ => le_max_right _ _) (fun edge => max_le_max (inequalities edge) le_rfl)

theorem nonnegativeElectricalTransfer_scale (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    {scalar : ℝ} (nonnegative : 0 ≤ scalar) :
    nonnegativeElectricalTransfer rule (fun marks => scalar*value marks) =
      fun marks => scalar*nonnegativeElectricalTransfer rule value marks := by
  unfold nonnegativeElectricalTransfer electricalTransfer
  funext marks
  have clipping (edge : Fin rule.edges) :
      max (scalar*value (innovationTreeShift rule [edge] marks)) 0 =
        scalar*max (value (innovationTreeShift rule [edge] marks)) 0 := by
    rw [mul_max_of_nonneg _ _ nonnegative, mul_zero]
  simp_rw [clipping]
  exact electricalCell_scale rule.network (marks ([], true)) (fun _ => le_max_right _ _) nonnegative

theorem nonnegativeElectricalTransferLp_smul (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint))
    (scalar : ℝ) (nonnegative : 0 ≤ scalar) :
    nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order (scalar • value) =
      scalar • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value := by
  have congruent := nonnegativeElectricalTransfer_congr_ae rule p positive belowOne fixedPoint
    (Lp.coeFn_smul scalar value)
  apply Lp.ext
  filter_upwards [nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order (scalar • value),
    Lp.coeFn_smul scalar (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value),
    nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order value, congruent]
    with marks firstEqual scalarEqual secondEqual transferEqual
  rw [firstEqual, transferEqual, scalarEqual, Pi.smul_apply, smul_eq_mul, secondEqual]
  change nonnegativeElectricalTransfer rule (fun sample => scalar * value sample) marks = scalar * nonnegativeElectricalTransfer rule value marks
  exact congrFun (nonnegativeElectricalTransfer_scale rule value nonnegative) marks

theorem nonnegativeElectricalTransferLp_monotone (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) :
    Monotone (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order) := by
  intro first second comparison
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order first,
    nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order second,
    nonnegativeElectricalTransfer_mono_ae rule p positive belowOne fixedPoint ((Lp.coeFn_le first second).mpr comparison)]
    with marks firstEquality secondEquality inequality
  simpa only [firstEquality, secondEquality] using inequality


end
end IGSIII34.Percolation
