import IGSIII34.Resistance.IntegralConductance

set_option autoImplicit false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory

theorem random_resistance_integral_lower_bound
    {Outcome Vertex Edge : Type*} [MeasurableSpace Outcome]
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (measure : Measure Outcome) [IsProbabilityMeasure measure]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure)
    (inverseIntegrable : ∀ edge, Integrable (fun outcome => (resistance outcome edge)⁻¹) measure)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ outcome, (resistance outcome edge)⁻¹ ∂measure) = inverseMean) :
    network.effectiveResistance (fun _ => 1) / inverseMean ≤
      ∫ outcome, network.effectiveResistance (resistance outcome) ∂measure := by
  have outputIntegrable := network.effectiveResistance_integrable measure connected resistance
    measurableInput positive inputIntegrable
  have outputInverseIntegrable := network.reciprocalResistance_integrable measure connected resistance
    measurableInput positive inverseIntegrable
  have reciprocalBound := network.reciprocalResistance_integral_upper_bound measure connected resistance
    measurableInput positive inverseIntegrable inverseMeanPositive commonInverseMean
  have unitResistancePositive := network.effectiveResistance_pos_of_connected connected (fun _ => zero_lt_one)
  let trialScalar := network.effectiveResistance (fun _ => 1) / inverseMean
  have pointwise (outcome : Outcome) :
      2 * trialScalar ≤ network.effectiveResistance (resistance outcome) +
        trialScalar ^ 2 * (network.effectiveResistance (resistance outcome))⁻¹ := by
    have outputPositive := network.effectiveResistance_pos_of_connected connected (positive outcome)
    apply (mul_le_mul_iff_of_pos_right outputPositive).mp
    have cancellation : trialScalar ^ 2 * (network.effectiveResistance (resistance outcome))⁻¹ *
        network.effectiveResistance (resistance outcome) = trialScalar ^ 2 := by
      rw [mul_assoc, inv_mul_cancel₀ outputPositive.ne', mul_one]
    rw [add_mul, cancellation]
    nlinarith [sq_nonneg (network.effectiveResistance (resistance outcome) - trialScalar)]
  have comparison := integral_mono (integrable_const (2 * trialScalar))
    (outputIntegrable.add (outputInverseIntegrable.const_mul (trialScalar ^ 2))) pointwise
  have constantIntegral : (∫ _outcome : Outcome, 2 * trialScalar ∂measure) = 2 * trialScalar := by simp
  rw [constantIntegral] at comparison
  simp only [Pi.add_apply] at comparison
  rw [integral_add outputIntegrable (outputInverseIntegrable.const_mul _), integral_const_mul] at comparison
  have productBound := mul_le_mul_of_nonneg_left reciprocalBound (sq_nonneg trialScalar)
  have scalarIdentity : trialScalar ^ 2 * (inverseMean / network.effectiveResistance (fun _ => 1)) =
      trialScalar := by
    dsimp [trialScalar]
    field_simp [unitResistancePositive.ne', inverseMeanPositive.ne']
  rw [scalarIdentity] at productBound
  change trialScalar ≤ _
  linarith

end
end IGSIII34.Resistance.FiniteNetwork
