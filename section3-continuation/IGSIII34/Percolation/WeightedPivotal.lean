import IGSIII34.Percolation.MeanResistance
import IGSIII34.Percolation.NormalizedLaw
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Universality.Percolation.StrictInstability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Resistance Resistance.FiniteNetwork
open scoped NNReal ENNReal

theorem weighted_pivotal_sum_le_electricalCell {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crosses : rule.crosses configuration = true) (input : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ input edge) :
    (∑ edge, if rule.pivotal configuration edge = true then input edge else 0) ≤
      electricalCell rule configuration input := by
  classical
  have openPivotal (edge : Fin edges) (pivotal : rule.pivotal configuration edge = true) :
      configuration edge = true := by
    rw [← rule.pivotal_crosses_eq_state configuration edge pivotal]
    exact crosses
  have bound := (network rule configuration).sum_pivotal_resistances_le_effectiveResistance
    ((network rule configuration).unitFlows_nonempty_of_connected (connected_of_crosses rule configuration crosses))
    (fun edge => nonnegative edge.val)
    (Finset.univ.filter fun edge => rule.pivotal configuration edge.val = true)
    (by
      intro edge membership
      exact pivotal_disconnects_open_network rule configuration edge (Finset.mem_filter.mp membership).2)
  simp only [Finset.sum_filter] at bound
  have sumEquality : (∑ edge : {edge : Fin edges // configuration edge = true},
      if rule.pivotal configuration edge.val = true then input edge.val else 0) =
      ∑ edge : Fin edges, if rule.pivotal configuration edge = true then input edge else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun edge => configuration edge = true)
      (p := fun edge => configuration edge = true)
      (f := fun edge : Fin edges => if rule.pivotal configuration edge = true then input edge else 0)
      (fun edge => by simp)]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases opened : configuration edge = true
    · simp only [opened, ↓reduceIte]
    · have notPivotal : rule.pivotal configuration edge ≠ true := fun pivotal => opened (openPivotal edge pivotal)
      simp [opened, notPivotal]
  rw [sumEquality] at bound
  exact bound

theorem connectedConfigurationLaw_pivotal_integral (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    (∫ configuration, (rule.network.pivotalCount configuration : ℝ)
      ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _)) =
        deriv rule.network.reliability parameter := by
  change (∫ configuration, (rule.network.pivotalCount configuration : ℝ)
    ∂(finiteWeightPMF (rule.network.conditionalCellWeight parameter true)
      (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true)
      (rule.network.sum_conditionalCellWeight parameter (by rwa [fixedPoint])
        (by rwa [fixedPoint]) true)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [finiteWeightPMF_apply, ENNReal.toReal_ofReal
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true _), smul_eq_mul]
  calc
    _ = expectation parameter (fun configuration => if rule.network.crosses configuration then
          (rule.network.pivotalCount configuration : ℝ) else 0) / rule.network.reliability parameter := by
      unfold expectation conditionalCellWeight
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro configuration _
      cases crossing : rule.network.crosses configuration <;> simp [crossing] <;> ring
    _ = _ := rule.network.conditional_connected_pivotalCount_at_fixed_point parameter fixedPoint positive.ne'

theorem iid_electricalCell_lintegral_pivotal_lower {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crosses : rule.crosses configuration = true) (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1) :
    (rule.pivotalCount configuration : ℝ≥0∞) ≤
      ∫⁻ input : Fin edges → ℝ≥0, (electricalCellNNReal rule configuration input : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0)) := by
  classical
  have pointwise (input : Fin edges → ℝ≥0) :
      (∑ edge, if rule.pivotal configuration edge = true then (input edge : ℝ≥0∞) else 0) ≤
        (electricalCellNNReal rule configuration input : ℝ≥0∞) := by
    calc
      _ = ENNReal.ofReal (∑ edge, if rule.pivotal configuration edge = true then (input edge : ℝ) else 0) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun edge _ => by split_ifs <;> positivity)]
        apply Finset.sum_congr rfl
        intro edge _
        split_ifs <;> simp
      _ ≤ ENNReal.ofReal (electricalCell rule configuration (fun edge => (input edge : ℝ))) :=
        ENNReal.ofReal_le_ofReal (weighted_pivotal_sum_le_electricalCell rule configuration crosses
          (fun edge => (input edge : ℝ)) (fun edge => (input edge).2))
      _ = _ := by
        change ENNReal.ofReal ((electricalCellNNReal rule configuration input : ℝ≥0) : ℝ) =
          (electricalCellNNReal rule configuration input : ℝ≥0∞)
        exact ENNReal.ofReal_coe_nnreal
  have lower : (∫⁻ input : Fin edges → ℝ≥0,
      (∑ edge, if rule.pivotal configuration edge = true then (input edge : ℝ≥0∞) else 0)
      ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0))) ≤
      ∫⁻ input : Fin edges → ℝ≥0, (electricalCellNNReal rule configuration input : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0)) := lintegral_mono pointwise
  rw [lintegral_finsetSum] at lower
  · have integralEquality (edge : Fin edges) :
        (∫⁻ input : Fin edges → ℝ≥0,
          (if rule.pivotal configuration edge = true then (input edge : ℝ≥0∞) else 0)
          ∂Measure.pi (fun _ : Fin edges => (law : Measure ℝ≥0))) =
            if rule.pivotal configuration edge = true then 1 else 0 := by
      by_cases pivotal : rule.pivotal configuration edge = true
      · simp only [pivotal, ↓reduceIte]
        exact ((measurePreserving_eval (fun _ : Fin edges => (law : Measure ℝ≥0)) edge).lintegral_comp
          measurable_id.coe_nnreal_ennreal).trans meanOne
      · simp [pivotal]
    simp only [integralEquality] at lower
    simpa only [pivotalCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using lower
  · intro edge _
    by_cases pivotal : rule.pivotal configuration edge = true
    · simp only [pivotal, ↓reduceIte]
      exact (measurable_pi_apply edge).coe_nnreal_ennreal
    · simp only [pivotal, ↓reduceIte]
      exact measurable_const

theorem connectedConfigurationLaw_crosses (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∀ᵐ configuration ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _),
      rule.network.crosses configuration = true := by
  apply ae_iff_of_countable.mpr
  intro configuration nonzero
  by_contra failure
  apply nonzero
  change (finiteWeightPMF (rule.network.conditionalCellWeight parameter true)
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    (rule.network.sum_conditionalCellWeight parameter (by rwa [fixedPoint])
      (by rwa [fixedPoint]) true)).toMeasure {configuration} = 0
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finiteWeightPMF_apply]
  simp [conditionalCellWeight, failure]

theorem electricalOutputLaw_lintegral_pivotal_lower (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1) :
    ENNReal.ofReal (deriv rule.network.reliability parameter) ≤
      ∫⁻ value, (value : ℝ≥0∞)
        ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0) := by
  have coefficientIdentity :
      ENNReal.ofReal (deriv rule.network.reliability parameter) =
        ∫⁻ configuration, (rule.network.pivotalCount configuration : ℝ≥0∞)
          ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := by
    rw [← connectedConfigurationLaw_pivotal_integral rule parameter positive belowOne fixedPoint]
    convert ofReal_integral_eq_lintegral_ofReal
      (μ := (connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _))
      (Integrable.of_finite
      (f := fun configuration => (rule.network.pivotalCount configuration : ℝ)))
      (ae_of_all _ (fun configuration => Nat.cast_nonneg _)) using 1
    apply lintegral_congr
    intro configuration
    exact (ENNReal.ofReal_natCast _).symm
  rw [coefficientIdentity]
  calc
    _ ≤ ∫⁻ configuration, ∫⁻ input : Fin rule.edges → ℝ≥0,
        (electricalCellNNReal rule.network configuration input : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := by
      apply lintegral_mono_ae
      filter_upwards [connectedConfigurationLaw_crosses rule parameter positive belowOne fixedPoint]
        with configuration crossing
      exact iid_electricalCell_lintegral_pivotal_lower rule.network configuration crossing law meanOne
    _ = _ := by
      change _ = ∫⁻ value, (value : ℝ≥0∞)
        ∂(((connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _).prod
          (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0)))).map
          (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
            electricalCellNNReal rule.network data.1 data.2))
      rw [lintegral_map (f := fun value : ℝ≥0 => (value : ℝ≥0∞)) measurable_id.coe_nnreal_ennreal
        (electricalCellNNReal_joint_continuous rule.network).measurable]
      exact (lintegral_prod _ (electricalCellNNReal_joint_continuous rule.network).measurable.coe_nnreal_ennreal.aemeasurable).symm

theorem electricalOutputMean_pivotal_lower (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (bound : ℝ≥0)
    (momentBound : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1) :
    deriv rule.network.reliability parameter ≤
      electricalOutputMean rule parameter positive belowOne fixedPoint law := by
  have outputIntegrable := IGSIII34.Probability.integrable_coe_of_secondMoment_bound
    (electricalOutputLaw rule parameter positive belowOne fixedPoint law) ((rule.edges : ℝ≥0) ^ 2 * bound)
    (electricalOutputLaw_secondMoment_bound rule parameter positive belowOne fixedPoint law bound momentBound)
  have integralEquality : (∫⁻ value, (value : ℝ≥0∞)
      ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) =
      ENNReal.ofReal (electricalOutputMean rule parameter positive belowOne fixedPoint law) :=
    lintegral_coe_eq_integral (fun value : ℝ≥0 => value) outputIntegrable
  have lower := electricalOutputLaw_lintegral_pivotal_lower rule parameter positive belowOne fixedPoint law meanOne
  rw [integralEquality] at lower
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun value : ℝ≥0 => value.2))).mp lower

theorem electricalOutputMean_positive_of_classical (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (bound : ℝ≥0)
    (momentBound : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1) :
    0 < electricalOutputMean rule parameter positive belowOne fixedPoint law :=
  zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable parameter positive belowOne
    fixedPoint classical.scale).trans_le
    (electricalOutputMean_pivotal_lower rule parameter positive belowOne fixedPoint law bound momentBound meanOne))

end
end IGSIII34.Percolation
