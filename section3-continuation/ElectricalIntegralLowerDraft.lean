import IGSIII34.Resistance.IntegralConductance
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII34.Resistance.FiniteNetwork

theorem electricalCell_inv_le_sum_inv {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ) (positive : ∀ edge, 0 < input edge) :
    (electricalCell network configuration input)⁻¹ ≤ ∑ edge, (input edge)⁻¹ := by
  by_cases crossing : network.crosses configuration = true
  · have connected := connected_of_crosses network configuration crossing
    change ((IGSIII34.Percolation.network network configuration).effectiveResistance (fun edge => input edge.val))⁻¹ ≤ _
    have conductanceEquality : (IGSIII34.Percolation.network network configuration).conductanceFunctional
        (fun edge => (input edge.val)⁻¹) =
        ((IGSIII34.Percolation.network network configuration).effectiveResistance (fun edge => input edge.val))⁻¹ := by
      simpa only [inv_inv, one_div] using
        (IGSIII34.Percolation.network network configuration).conductanceFunctional_eq_reciprocalResistance connected
          (fun edge => inv_pos.mpr (positive edge.val))
    rw [← conductanceEquality]
    exact ((IGSIII34.Percolation.network network configuration).conductanceFunctional_le_sum_conductances
      (fun edge => (inv_pos.mpr (positive edge.val)).le)).trans
      (sum_open_edges_le_sum configuration (fun edge => (input edge)⁻¹) (fun edge => (inv_pos.mpr (positive edge)).le))
  · rw [electricalCell_eq_zero_of_not_crosses network configuration crossing, inv_zero]
    exact Finset.sum_nonneg (fun edge _ => (inv_pos.mpr (positive edge)).le)

theorem electricalCell_integral_mean_lower
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crossing : network.crosses configuration = true)
    (input : Sample → Fin edges → ℝ) (measurable : Measurable input) (positive : ∀ sample edge, 0 < input sample edge)
    (inputIntegrable : ∀ edge, Integrable (fun sample => input sample edge) measure)
    (inverseIntegrable : ∀ edge, Integrable (fun sample => (input sample edge)⁻¹) measure)
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ sample, (input sample edge)⁻¹ ∂measure) = inverseMean) :
    unitConfigurationResistance network configuration / inverseMean ≤
      ∫ sample, electricalCell network configuration (input sample) ∂measure := by
  have connected := connected_of_crosses network configuration crossing
  have outputIntegrable : Integrable (fun sample => electricalCell network configuration (input sample)) measure := (IGSIII34.Percolation.network network configuration).effectiveResistance_integrable
    measure connected (fun sample edge => input sample edge.val)
    (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).comp measurable))
    (fun sample edge => positive sample edge.val) (fun edge => inputIntegrable edge.val)
  have outputInverseIntegrable : Integrable (fun sample => (electricalCell network configuration (input sample))⁻¹) measure := (IGSIII34.Percolation.network network configuration).reciprocalResistance_integrable
    measure connected (fun sample edge => input sample edge.val)
    (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).comp measurable))
    (fun sample edge => positive sample edge.val) (fun edge => inverseIntegrable edge.val)
  have reciprocalBound : (∫ sample, (electricalCell network configuration (input sample))⁻¹ ∂measure) ≤
      inverseMean / unitConfigurationResistance network configuration := (IGSIII34.Percolation.network network configuration).reciprocalResistance_integral_upper_bound
    measure connected (fun sample edge => input sample edge.val)
    (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).comp measurable))
    (fun sample edge => positive sample edge.val) (fun edge => inverseIntegrable edge.val)
    inverseMeanPositive (fun edge => commonInverseMean edge.val)
  have unitPositive : 0 < unitConfigurationResistance network configuration := (IGSIII34.Percolation.network network configuration).effectiveResistance_pos_of_connected connected (fun _ => zero_lt_one)
  let trialScalar := unitConfigurationResistance network configuration / inverseMean
  have pointwise (sample : Sample) : 2*trialScalar ≤ electricalCell network configuration (input sample) +
      trialScalar^2*(electricalCell network configuration (input sample))⁻¹ := by
    have outputPositive : 0 < electricalCell network configuration (input sample) := (IGSIII34.Percolation.network network configuration).effectiveResistance_pos_of_connected connected
      (fun edge => positive sample edge.val)
    apply (mul_le_mul_iff_of_pos_right outputPositive).mp
    have cancellation : trialScalar^2*(electricalCell network configuration (input sample))⁻¹*
        electricalCell network configuration (input sample) = trialScalar^2 := by
      rw [mul_assoc, inv_mul_cancel₀ outputPositive.ne', mul_one]
    rw [add_mul, cancellation]
    nlinarith [sq_nonneg (electricalCell network configuration (input sample)-trialScalar)]
  have comparison := integral_mono (integrable_const (2*trialScalar))
    (outputIntegrable.add (outputInverseIntegrable.const_mul (trialScalar^2))) pointwise
  change (∫ _sample : Sample, 2*trialScalar ∂measure) ≤
    ∫ sample, electricalCell network configuration (input sample) + trialScalar^2*(electricalCell network configuration (input sample))⁻¹ ∂measure at comparison
  rw [integral_add outputIntegrable (outputInverseIntegrable.const_mul _), integral_const_mul] at comparison
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at comparison
  simp only [integral_const_mul] at comparison
  have productBound := mul_le_mul_of_nonneg_left reciprocalBound (sq_nonneg trialScalar)
  have scalarIdentity : trialScalar^2*(inverseMean/unitConfigurationResistance network configuration) = trialScalar := by
    dsimp [trialScalar]
    field_simp [unitPositive.ne', inverseMeanPositive.ne']
  rw [scalarIdentity] at productBound
  change trialScalar ≤ _
  linarith

end
end IGSIII34.Percolation
