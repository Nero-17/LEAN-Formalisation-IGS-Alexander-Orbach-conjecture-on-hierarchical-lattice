import IGSIII34.Percolation.RealMomentsEigenlaw
import IGSIII34.Percolation.ScalingEigenlaw
import IGSIII34.Resistance.NonnegativeJensen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Resistance.FiniteNetwork
open scoped NNReal ENNReal

theorem iid_electricalCell_integral_le_unit {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crosses : rule.crosses configuration = true) (law : ProbabilityMeasure ℝ≥0)
    (inputIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1) :
    (∫ input : Fin edges → ℝ≥0, (electricalCellNNReal rule configuration input : ℝ)
      ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0))) ≤
      configurationResistance rule configuration := by
  have coordinateIntegrable (edge : Fin edges) :
      Integrable (fun input : Fin edges → ℝ≥0 => (input edge : ℝ))
        (Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0))) :=
    (measurePreserving_eval (fun _ : Fin edges => (law : Measure ℝ≥0)) edge).integrable_comp_of_integrable inputIntegrable
  have coordinateMean (edge : Fin edges) :
      (∫ input : Fin edges → ℝ≥0, (input edge : ℝ)
        ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0))) = 1 := by
    have preserving := measurePreserving_eval (fun _ : Fin edges => (law : Measure ℝ≥0)) edge
    have mapped := integral_map (μ := Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0)))
      (φ := fun input : Fin edges → ℝ≥0 => input edge)
      (f := fun value : ℝ≥0 => (value : ℝ)) preserving.measurable.aemeasurable
      NNReal.continuous_coe.measurable.aestronglyMeasurable
    rw [preserving.map_eq] at mapped
    exact mapped.symm.trans meanOne
  have comparison := (network rule configuration).nonnegative_resistance_integral_jensen
    (Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0)))
    (connected_of_crosses rule configuration crosses)
    (fun input edge => (input edge.val : ℝ))
    (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).coe_nnreal_real))
    (fun input edge => (input edge.val).2) (fun edge => coordinateIntegrable edge.val)
  simp only [coordinateMean] at comparison
  exact comparison

theorem electricalOutputMean_le_conditional_unit (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (inputIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1) :
    electricalOutputMean rule parameter positive belowOne fixedPoint law ≤
      ∫ configuration, configurationResistance rule.network configuration
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := by
  have jointIntegrable : Integrable
      (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
        (electricalCellNNReal rule.network data.1 data.2 : ℝ))
      (electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _) := by
    apply (integrable_finsetSum Finset.univ (fun edge _ =>
      (electricalInputLaw_coordinate_preserving rule parameter positive belowOne fixedPoint law edge).integrable_comp_of_integrable inputIntegrable)).mono'
      (NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous rule.network)).measurable.aestronglyMeasurable
    filter_upwards [] with data
    change |(electricalCellNNReal rule.network data.1 data.2 : ℝ)| ≤ ∑ edge, (data.2 edge : ℝ)
    calc
      _ = (electricalCellNNReal rule.network data.1 data.2 : ℝ) := NNReal.abs_eq _
      _ ≤ _ := electricalCell_le_sum rule.network data.1 (fun edge => (data.2 edge).2)
  have meanIdentity : electricalOutputMean rule parameter positive belowOne fixedPoint law =
      ∫ configuration, ∫ input : Fin rule.edges → ℝ≥0,
        (electricalCellNNReal rule.network configuration input : ℝ)
        ∂Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := by
    unfold electricalOutputMean electricalOutputLaw
    rw [ProbabilityMeasure.toMeasure_map]
    rw [integral_map (electricalCellNNReal_joint_continuous rule.network).measurable.aemeasurable
      NNReal.continuous_coe.measurable.aestronglyMeasurable]
    exact integral_prod _ jointIntegrable
  rw [meanIdentity]
  apply integral_mono_ae jointIntegrable.integral_prod_left (Integrable.of_finite)
  filter_upwards [connectedConfigurationLaw_crosses rule parameter positive belowOne fixedPoint]
    with configuration crosses
  exact iid_electricalCell_integral_le_unit rule.network configuration crosses law inputIntegrable meanOne

theorem electricalOutputMean_le_expected_path_length (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (inputIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    electricalOutputMean rule parameter positive belowOne fixedPoint law ≤
      ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := by
  apply (electricalOutputMean_le_conditional_unit rule parameter positive belowOne fixedPoint law
    inputIntegrable meanOne).trans
  apply integral_mono_ae (Integrable.of_finite) (Integrable.of_finite)
  filter_upwards [connectedConfigurationLaw_crosses rule parameter positive belowOne fixedPoint]
    with configuration crosses
  exact ((network rule.network configuration).unitResistance_le_distance
    (connected_of_crosses rule.network configuration crosses)).trans
    (by exact_mod_cast distanceBound configuration crosses)

end
end IGSIII34.Percolation
