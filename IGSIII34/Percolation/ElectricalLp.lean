import IGSIII34.Percolation.ElectricalTransfer
import IGSIII.Chemical.TransferContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped ENNReal NNReal

-- The positive-part extension permits an operator on the whole Lp space.
-- It agrees with the physical transfer on nonnegative inputs.
def nonnegativeElectricalTransfer (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) :=
  electricalTransfer rule (fun marks => max (value marks) 0)

theorem electricalCell_positivePart_dispatch_measurable {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) :
    Measurable (fun data : Configuration edges × (Fin edges → ℝ) =>
      electricalCell network data.1 (fun edge => max (data.2 edge) 0)) := by
  apply measurable_from_prod_countable_right
  intro configuration
  have clipped : Continuous (fun input : Fin edges → ℝ =>
      (⟨fun edge => max (input edge) 0, fun edge => le_max_right _ _⟩ :
        {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge})) := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun edge => (continuous_apply edge).max continuous_const)
  exact ((electricalCell_continuous_nonnegative network configuration).comp clipped).measurable

theorem nonnegativeElectricalTransfer_memLp (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    {order : ℝ≥0∞}
    (integrable : MemLp value order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    MemLp (nonnegativeElectricalTransfer rule value) order
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have children (edge : Fin rule.edges) :=
    innovationTreeShift_memLp rule p positive belowOne fixedPoint [edge] integrable
  have measurable : AEStronglyMeasurable (nonnegativeElectricalTransfer rule value)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ((electricalCell_positivePart_dispatch_measurable rule.network).comp_aemeasurable
      ((measurable_pi_apply ([], true)).aemeasurable.prodMk
        (aemeasurable_pi_lambda _ (fun edge => (children edge).aestronglyMeasurable.aemeasurable)))).aestronglyMeasurable
  have envelope : MemLp (fun marks => ∑ edge : Fin rule.edges,
      ‖value (innovationTreeShift rule [edge] marks)‖) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    memLp_finsetSum _ (fun edge _ => (children edge).norm)
  apply envelope.mono' measurable
  filter_upwards [] with marks
  unfold nonnegativeElectricalTransfer
  rw [Real.norm_eq_abs, abs_of_nonneg (electricalTransfer_nonnegative rule
    (fun marks => max (value marks) 0) (fun _ => le_max_right _ _) marks)]
  exact (electricalCell_le_sum rule.network (marks ([], true))
    (fun _ => le_max_right _ _)).trans (Finset.sum_le_sum (fun edge _ => by
      rw [Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)))

def nonnegativeElectricalTransferLp (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (nonnegativeElectricalTransfer_memLp rule p positive belowOne fixedPoint (Lp.memLp value)).toLp
    (nonnegativeElectricalTransfer rule value)

theorem nonnegativeElectricalTransferLp_coe_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ⇑(nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] nonnegativeElectricalTransfer rule value :=
  MemLp.coeFn_toLp _

end
end IGSIII34.Percolation
