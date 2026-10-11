import IGSIII34.Percolation.ConfigurationVariance
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators ENNReal

theorem finite_probability_integral_eq_finiteMean {State : Type*} [Fintype State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (measure : Measure State) [IsProbabilityMeasure measure] (response : State → ℝ) :
    (∫ state, response state ∂measure) = finiteMean (fun state => (measure {state}).toReal) response := by
  have equality := PMF.integral_eq_sum measure.toPMF response
  rw [Measure.toPMF_toMeasure] at equality
  simpa only [finiteMean, Measure.toPMF_apply, smul_eq_mul] using equality

theorem finite_probability_weights_normalized {State : Type*} [Fintype State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (measure : Measure State) [IsProbabilityMeasure measure] :
    ∑ state, (measure {state}).toReal = 1 := by
  have equality := finite_probability_integral_eq_finiteMean measure (fun _ => 1)
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, finiteMean, mul_one] using equality.symm

theorem finite_probability_pi_integral_eq_finiteMean {State : Type*} [Fintype State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (measure : Measure State) [IsProbabilityMeasure measure] (count : ℕ)
    (response : (Fin count → State) → ℝ) :
    (∫ input, response input ∂Measure.pi (fun _ : Fin count => measure)) =
      finiteMean (IGSIII34.Probability.tupleWeight (fun _ state => (measure {state}).toReal)) response := by
  rw [finite_probability_integral_eq_finiteMean]
  simp only [Measure.pi_singleton, ENNReal.toReal_prod, IGSIII34.Probability.tupleWeight]
  rfl

theorem finite_probability_electricalCell_variance_le_product_moments
    {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    (measure : Measure State) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : network.crosses configuration = true)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) (inverseMoment : ℝ)
    (inverseBound : (∫ state, (resistance state)⁻¹^power ∂measure) ≤ inverseMoment) :
    (∫ input, (electricalCell network configuration (fun edge => resistance (input edge)) -
      ∫ input, electricalCell network configuration (fun edge => resistance (input edge))
        ∂Measure.pi (fun _ : Fin edges => measure))^2 ∂Measure.pi (fun _ : Fin edges => measure)) ≤
      2*(∫ state, resistance state^2 ∂measure) *
        (∫ input, electricalCell network configuration (fun edge => resistance (input edge))^2
          ∂Measure.pi (fun _ : Fin edges => measure))^(1/(2:ℝ)) *
            ((edges:ℝ)*inverseMoment)^(1/power) := by
  rw [finite_probability_pi_integral_eq_finiteMean, finite_probability_pi_integral_eq_finiteMean,
    finite_probability_integral_eq_finiteMean, finite_probability_pi_integral_eq_finiteMean]
  change finiteVariance (IGSIII34.Probability.tupleWeight (fun _ : Fin edges => fun state => (measure {state}).toReal))
    (fun input => electricalCell network configuration (fun edge => resistance (input edge))) ≤ _
  apply finite_electricalCell_variance_le_product_moments network configuration crosses
    (fun state => (measure {state}).toReal) (fun state => ENNReal.toReal_nonneg)
    (finite_probability_weights_normalized measure) resistance positive powerAtLeastTwo inverseMoment
  simpa only [finite_probability_integral_eq_finiteMean] using inverseBound

end
end IGSIII34.Percolation
