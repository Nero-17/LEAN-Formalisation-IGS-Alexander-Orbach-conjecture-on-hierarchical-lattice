import IGSIII34.Probability.MixedMoments
import IGSIII34.Percolation.WeightedPivotal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Resistance.FiniteNetwork
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

theorem electricalCellNNReal_le_sum {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ≥0) :
    electricalCellNNReal rule configuration input ≤ ∑ edge, input edge := by
  apply NNReal.coe_le_coe.mp
  change electricalCell rule configuration (fun edge => (input edge : ℝ)) ≤
    ((∑ edge, input edge : ℝ≥0) : ℝ)
  convert electricalCell_le_sum rule configuration (fun edge => (input edge).2) using 1
  congr 1
  exact NNReal.coe_sum Finset.univ input

theorem electricalOutputLaw_powerMoment_le_iid_sum (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (power : ℕ) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power
      ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) ≤
        ∫⁻ input : Fin rule.edges → ℝ≥0, (∑ edge, (input edge : ℝ≥0∞)) ^ power
          ∂Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0)) := by
  change (∫⁻ value, (value : ℝ≥0∞) ^ power
    ∂((electricalInputLaw rule parameter positive belowOne fixedPoint law :
      Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
        (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
          electricalCellNNReal rule.network data.1 data.2))) ≤ _
  rw [lintegral_map (f := fun value : ℝ≥0 => (value : ℝ≥0∞) ^ power)
    (measurable_id.coe_nnreal_ennreal.pow_const power)
    (electricalCellNNReal_joint_continuous rule.network).measurable]
  calc
    _ ≤ ∫⁻ data : Configuration rule.edges × (Fin rule.edges → ℝ≥0),
        (∑ edge, (data.2 edge : ℝ≥0∞)) ^ power
        ∂(electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _) := by
      apply lintegral_mono
      intro data
      apply pow_le_pow_left'
      convert ENNReal.coe_le_coe.mpr (electricalCellNNReal_le_sum rule.network data.1 data.2)
        using 1 <;> norm_cast
    _ = _ := by
      have preserving : MeasurePreserving Prod.snd
          (electricalInputLaw rule parameter positive belowOne fixedPoint law :
            Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0)))
          (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))) :=
        measurePreserving_snd
      exact preserving.lintegral_comp
        ((Finset.measurable_sum Finset.univ (fun edge _ =>
          (measurable_pi_apply edge).coe_nnreal_ennreal)).pow_const power)

theorem electricalOutputLaw_powerMoment_bound (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) (bound : ℝ≥0) (boundAtLeastOne : 1 ≤ bound)
    (highMomentBound : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bound) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power
      ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) ≤
        (rule.edges : ℝ≥0∞) * bound + (rule.edges : ℝ≥0∞) ^ power *
          (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  refine (electricalOutputLaw_powerMoment_le_iid_sum rule parameter positive belowOne fixedPoint law power).trans
    ((IGSIII34.Probability.iid_sum_power_moment_bound (Edge := Fin rule.edges) law meanOne
      powerAtLeastTwo bound boundAtLeastOne highMomentBound).trans ?_)
  simp only [Fintype.card_fin]
  exact add_le_add (mul_le_mul_left' highMomentBound _) le_rfl

theorem normalizedElectricalLaw_powerMoment_bound (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) (bound : ℝ≥0) (boundAtLeastOne : 1 ≤ bound)
    (highMomentBound : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bound)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1)
    (coefficient : ℝ≥0) (coefficientPositive : 0 < coefficient)
    (meanLower : (coefficient : ℝ) ≤ electricalOutputMean rule parameter positive belowOne fixedPoint law) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power
      ∂(normalizedElectricalLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) ≤
        ((coefficient : ℝ≥0∞) ^ power)⁻¹ *
          ((rule.edges : ℝ≥0∞) * bound + (rule.edges : ℝ≥0∞) ^ power *
            (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) := by
  unfold normalizedElectricalLaw
  rw [scaledProbabilityLaw_moment]
  have coefficientPositive' : (0 : ℝ) < coefficient := by exact_mod_cast coefficientPositive
  have meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law :=
    coefficientPositive'.trans_le meanLower
  have inverseBound : Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ ≤
      coefficient⁻¹ := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr meanPositive.le), NNReal.coe_inv]
    exact inv_anti₀ (by exact_mod_cast coefficientPositive) meanLower
  have boundPower : ((Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ power ≤
      ((coefficient : ℝ≥0∞) ^ power)⁻¹ := by
    calc
      _ ≤ ((coefficient⁻¹ : ℝ≥0) : ℝ≥0∞) ^ power :=
        pow_le_pow_left' (ENNReal.coe_le_coe.mpr inverseBound) power
      _ = _ := by rw [ENNReal.coe_inv coefficientPositive.ne', ← ENNReal.inv_pow]
  exact mul_le_mul' boundPower
    (electricalOutputLaw_powerMoment_bound rule parameter positive belowOne fixedPoint law meanOne
      powerAtLeastTwo bound boundAtLeastOne highMomentBound)

end
end IGSIII34.Percolation
