import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
variable {Sample Prefix Boundary : Type*} [MeasurableSpace Sample] [MeasurableSpace Prefix]
    [MeasurableSpace Boundary] [StandardBorelSpace Boundary] [Nonempty Boundary]

theorem independent_pair_condExp_eq_integral (measure : Measure Sample) [IsProbabilityMeasure measure]
    (history : Sample → Prefix) (boundary : Sample → Boundary)
    (prefixMeasurable : Measurable history) (boundaryMeasurable : Measurable boundary)
    (independent : IndepFun history boundary measure)
    (response : Prefix × Boundary → ℝ) (responseMeasurable : StronglyMeasurable response)
    (responseIntegrable : Integrable (fun sample => response (history sample, boundary sample)) measure) :
    measure[fun sample => response (history sample, boundary sample) |
      (inferInstance : MeasurableSpace Prefix).comap history] =ᵐ[measure]
      fun sample => ∫ input, response (history sample, input) ∂measure.map boundary := by
  have joint := independent.map_prod_eq_prod_map_map prefixMeasurable.aemeasurable boundaryMeasurable.aemeasurable
  have kernelEquality := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := measure) prefixMeasurable boundaryMeasurable
    (κ := Kernel.const Prefix (measure.map boundary)) (by rw [Measure.compProd_const]; exact joint)
  have almostKernel := ae_of_ae_map prefixMeasurable.aemeasurable kernelEquality
  have conditional := condExp_prod_ae_eq_integral_condDistrib prefixMeasurable boundaryMeasurable.aemeasurable
    responseMeasurable responseIntegrable
  filter_upwards [conditional, almostKernel] with sample equality kernel
  rw [equality, kernel]
  rfl

end
end IGSIII34.Probability
