import IGSIII34.Diffusion.IntegerJ1ToUsualLocalJ1

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- Integer-horizon weak convergence tests every bounded real function
continuous for the standard local-J1 window criterion. Measurability
follows from the proved identity continuity and is not an extra input.
The limiting probability law may charge discontinuous paths. -/
theorem integerJ1_weak_integral_usualLocalJ1
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (weak : Tendsto laws atTop (𝓝 law))
    (test : SkorokhodCadlagPathCompletion Space → ℝ)
    (bound : ℝ) (bounded : ∀ path, |test path| ≤ bound)
    (continuity : usualLocalJ1SequentiallyContinuousTest test) :
    Tendsto (fun index => ∫ path, test path ∂(laws index : Measure (SkorokhodCadlagPathCompletion Space)))
      atTop (𝓝 (∫ path, test path ∂(law : Measure (SkorokhodCadlagPathCompletion Space)))) := by
  have integerContinuity := usualLocalJ1Test_integer_continuous test continuity
  exact probability_weak_integral_bounded_ae_continuous laws law weak test
    integerContinuity.measurable bound bounded
    (Eventually.of_forall (fun _ => integerContinuity.continuousAt))

end
end IGSIII34.Diffusion
