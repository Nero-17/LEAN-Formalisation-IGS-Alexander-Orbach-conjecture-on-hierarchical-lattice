import IGSIII34.Percolation.PhysicalOrbit
import IGSIII34.Percolation.ScalingEigenlaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

theorem electricalOutputLaw_scaled (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (scalar : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) :
    electricalOutputLaw rule p positive belowOne fixedPoint (scaledProbabilityLaw scalar law) =
      scaledProbabilityLaw scalar (electricalOutputLaw rule p positive belowOne fixedPoint law) := by
  have childLaw : (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))).map
      (fun input edge => scalar*input edge) =
      Measure.pi (fun _ : Fin rule.edges => (scaledProbabilityLaw scalar law : Measure ℝ≥0)) := by
    simp only [scaledProbabilityLaw_measure]
    exact Measure.pi_map_pi (fun _ => (measurable_const.mul measurable_id).aemeasurable)
  have inputLaw : (electricalInputLaw rule p positive belowOne fixedPoint (scaledProbabilityLaw scalar law) :
      Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))) =
      (electricalInputLaw rule p positive belowOne fixedPoint law :
        Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
        (fun data => (data.1, fun edge => scalar*data.2 edge)) := by
    change _ = ((connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure (Configuration rule.edges)).prod
      (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0)))).map
        (Prod.map id (fun input edge => scalar*input edge))
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, childLaw]
    rfl
  apply Subtype.ext
  change (electricalInputLaw rule p positive belowOne fixedPoint (scaledProbabilityLaw scalar law) : Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
    (fun data => electricalCellNNReal rule.network data.1 data.2) =
      (scaledProbabilityLaw scalar (electricalOutputLaw rule p positive belowOne fixedPoint law) : Measure ℝ≥0)
  rw [inputLaw, Measure.map_map (electricalCellNNReal_joint_continuous rule.network).measurable (by fun_prop),
    scaledProbabilityLaw_measure]
  change _ = ((electricalInputLaw rule p positive belowOne fixedPoint law : Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
    (fun data => electricalCellNNReal rule.network data.1 data.2)).map (fun value => scalar*value)
  rw [Measure.map_map (g := fun value : ℝ≥0 => scalar*value)
    (f := fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) => electricalCellNNReal rule.network data.1 data.2)
    (measurable_const.mul measurable_id)
    (electricalCellNNReal_joint_continuous rule.network).measurable]
  congr 1
  funext data
  exact electricalCellNNReal_scale rule.network data.1 data.2 scalar

theorem electricalOutputLaw_iterate_eigenlaw (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (electricalOutputLaw rule p positive belowOne fixedPoint)^[depth] law = scaledProbabilityLaw (growth^depth) law := by
  induction depth with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero] using (scaledProbabilityLaw_one law).symm
  | succ depth previous =>
      rw [Function.iterate_succ_apply', previous, electricalOutputLaw_scaled, eigenlaw, scaledProbabilityLaw_comp,
        pow_succ]

theorem electricalOutputLaw_iterate_eigenlaw_mean (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (meanOne : (∫ sample : ℝ≥0, (sample:ℝ) ∂(law:Measure ℝ≥0)) = 1) (depth : ℕ) :
    (∫ sample : ℝ≥0, (sample:ℝ) ∂((electricalOutputLaw rule p positive belowOne fixedPoint)^[depth] law : Measure ℝ≥0)) =
      (growth:ℝ)^depth := by
  rw [electricalOutputLaw_iterate_eigenlaw rule p positive belowOne fixedPoint law growth eigenlaw depth,
    scaledProbabilityLaw_mean, meanOne, mul_one, NNReal.coe_pow]

end
end IGSIII34.Percolation
