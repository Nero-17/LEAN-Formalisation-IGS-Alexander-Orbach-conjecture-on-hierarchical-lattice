import IGSIII4.HarmonicMeanLower
import IGSIII34.Percolation.LawMap
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII34.Percolation IGSIII34.Resistance IGSIII34.Resistance.FiniteNetwork
open scoped NNReal

theorem electricalCellNNReal_integrable {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (input : Sample → Fin edges → ℝ≥0)
    (measurable : Measurable input)
    (inputIntegrable : ∀ edge, Integrable (fun sample => (input sample edge : ℝ)) measure) :
    Integrable (fun sample => (electricalCellNNReal network configuration (input sample) : ℝ)) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inputIntegrable edge)).mono'
    (measurable_coe_nnreal_real.comp
      ((electricalCellNNReal_continuous network configuration).measurable.comp measurable)).aestronglyMeasurable
  filter_upwards [] with sample
  change ‖(electricalCellNNReal network configuration (input sample) : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (electricalCellNNReal network configuration (input sample)).coe_nonneg]
  exact electricalCell_le_sum network configuration (fun edge => (input sample edge).coe_nonneg)

theorem electricalCellNNReal_integral_lower_bound {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (input : Sample → Fin edges → ℝ≥0) (measurable : Measurable input)
    (positive : ∀ sample edge, 0 < (input sample edge : ℝ))
    (inputIntegrable : ∀ edge, Integrable (fun sample => (input sample edge : ℝ)) measure)
    (inverseIntegrable : ∀ edge, Integrable (fun sample => (input sample edge : ℝ)⁻¹) measure)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ sample, (input sample edge : ℝ)⁻¹ ∂measure) = inverseMean) :
    unitConfigurationResistance network configuration / inverseMean ≤
      ∫ sample, (electricalCellNNReal network configuration (input sample) : ℝ) ∂measure := by
  exact (IGSIII34.Percolation.network network configuration).random_resistance_integral_lower_bound
    measure (connected_of_crosses network configuration crossing)
    (fun sample edge => (input sample edge.val : ℝ))
    (measurable_pi_lambda _ (fun edge => measurable_coe_nnreal_real.comp
      ((measurable_pi_apply edge.val).comp measurable)))
    (fun sample edge => positive sample edge.val)
    (fun edge => inputIntegrable edge.val) (fun edge => inverseIntegrable edge.val)
    inverseMeanPositive (fun edge => commonInverseMean edge.val)

end
end IGSIII4
