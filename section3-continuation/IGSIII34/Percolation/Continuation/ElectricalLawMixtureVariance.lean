import IGSIII34.Percolation.Continuation.ElectricalLawVariance
import IGSIII.Chemical.GeodesicMixtureEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped NNReal ENNReal BigOperators

theorem electricalCell_law_mixture_variance_le_product_moments {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (configurationLaw : Measure (Configuration edges)) [IsProbabilityMeasure configurationLaw]
    (supported : ∀ configuration, network.crosses configuration ≠ true → configurationLaw {configuration} = 0)
    (law : ProbabilityMeasure ℝ≥0) (positive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) :
    (∫ configuration, (∫ input : Fin edges → ℝ≥0,
        electricalCell network configuration (fun edge => (input edge:ℝ))^2
        ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) -
      (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ))
        ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)))^2 ∂configurationLaw) ≤
      2*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
        (∫ configuration, ∫ input : Fin edges → ℝ≥0,
          electricalCell network configuration (fun edge => (input edge:ℝ))^2
            ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)) ∂configurationLaw)^(1/(2:ℝ)) *
        ((edges:ℝ)*(∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0)))^(1/power) := by
  let weight (configuration : Configuration edges) := (configurationLaw {configuration}).toReal
  let second (configuration : Configuration edges) := ∫ input : Fin edges → ℝ≥0,
    electricalCell network configuration (fun edge => (input edge:ℝ))^2
      ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))
  let mean (configuration : Configuration edges) := ∫ input : Fin edges → ℝ≥0,
    electricalCell network configuration (fun edge => (input edge:ℝ))
      ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))
  let secondMoment := ∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)
  let inverseMoment := ∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0)
  have secondNonnegative (configuration : Configuration edges) : 0 ≤ second configuration :=
    integral_nonneg (fun _ => sq_nonneg _)
  have secondMomentNonnegative : 0 ≤ secondMoment := integral_nonneg (fun _ => sq_nonneg _)
  have inverseMomentNonnegative : 0 ≤ inverseMoment := integral_nonneg (fun value =>
    Real.rpow_nonneg (inv_nonneg.mpr value.property) _)
  have rootBound := IGSIII.Chemical.finiteMean_sqrt_rpow_le weight second
    (fun _ => ENNReal.toReal_nonneg) (finite_probability_weights_normalized configurationLaw) secondNonnegative
  rw [finite_probability_integral_eq_finiteMean configurationLaw,
    finite_probability_integral_eq_finiteMean configurationLaw]
  change finiteMean weight (fun configuration => second configuration-mean configuration^2) ≤
    2*secondMoment*(finiteMean weight second)^(1/(2:ℝ))*((edges:ℝ)*inverseMoment)^(1/power)
  calc
    _ ≤ finiteMean weight (fun configuration =>
        2*secondMoment*(second configuration)^(1/(2:ℝ))*((edges:ℝ)*inverseMoment)^(1/power)) := by
      unfold finiteMean
      apply Finset.sum_le_sum
      intro configuration _
      by_cases crossing : network.crosses configuration = true
      · exact mul_le_mul_of_nonneg_left
          (electricalCell_law_variance_le_product_moments network configuration crossing law positive moments powerAtLeastTwo)
          ENNReal.toReal_nonneg
      · simp only [weight, supported configuration crossing, ENNReal.toReal_zero, zero_mul, le_refl]
    _ = 2*secondMoment*finiteMean weight (fun configuration => (second configuration)^(1/(2:ℝ)))*
        ((edges:ℝ)*inverseMoment)^(1/power) := by
      unfold finiteMean
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left rootBound (mul_nonneg (by norm_num) secondMomentNonnegative))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)

end
end IGSIII34.Percolation
