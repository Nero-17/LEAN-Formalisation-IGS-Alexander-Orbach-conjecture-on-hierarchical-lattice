import IGSIII34.Diffusion.OriginalJointAnnealedCoordinateUsualTests
import IGSIII34.Diffusion.CompletedEnvironmentOriginalJointIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Environment : Type*} [environmentMeasurable : MeasurableSpace Environment]
  [MetricSpace Environment] [SecondCountableTopology Environment] [BorelSpace Environment]

/-- The original, uncompleted environmental joint laws satisfy all
bounded measurable usual joint tests for the SAME completed limit kernel. -/
theorem original_environment_joint_usual_tests_of_completed_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment OriginalJointCompactSpace)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel (NullMeasurableSpace Environment environmentLaw) OriginalJointCompactSpace)
    [IsMarkovKernel limit]
    (quenched : ∀ᵐ environment ∂environmentLaw.completion,
      Tendsto (fun depth => conditionalKernelProbability
        (completedEnvironmentKernel environmentLaw (kernels depth)) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment)))
    (regular : ∀ᵐ environment ∂environmentLaw.completion,
      OriginalJointUsualTestRegular (conditionalKernelProbability limit environment))
    (test : Environment × OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ≥0) (bounded : ∀ point, ‖test point‖ ≤ bound)
    (usualContinuous : ∀ value, OriginalJointUsualSequentiallyContinuousTest
      (fun point => test (value, point))) :
    Tendsto (fun depth => ∫ point, test point ∂(environmentLaw ⊗ₘ kernels depth)) atTop
      (𝓝 (∫ point, test point ∂
        (@coordinateStateKernel (NullMeasurableSpace Environment environmentLaw) Environment
          OriginalJointCompactSpace inferInstance environmentMeasurable inferInstance (fun point => point)
          (completedEnvironmentIdentity_measurable environmentLaw) limit ∘ₘ environmentLaw.completion))) := by
  have convergence := @annealed_coordinate_original_joint_usual_tests_of_quenched
    (NullMeasurableSpace Environment environmentLaw) Environment
    inferInstance inferInstance inferInstance environmentMeasurable inferInstance
    environmentLaw.completion inferInstance (fun point => point)
    (completedEnvironmentIdentity_measurable environmentLaw)
    (fun depth => completedEnvironmentKernel environmentLaw (kernels depth))
    inferInstance limit inferInstance quenched regular test measurable bound bounded usualContinuous
  simpa only [completedEnvironment_original_joint_measure_identity] using convergence

end
end IGSIII34.Diffusion
