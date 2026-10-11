import IGSIII34.Diffusion.OriginalJointAnnealedCoordinateUsualTests
import IGSIII34.Diffusion.CompletedEnvironmentKernelLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Environment Coordinate State : Type*} [environmentMeasurable : MeasurableSpace Environment]
  [MetricSpace Coordinate] [SecondCountableTopology Coordinate]
  [MeasurableSpace Coordinate] [BorelSpace Coordinate]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

theorem completedEnvironment_coordinate_joint_identity
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    coordinateStateKernel (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
      (measurable.comp (completedEnvironmentIdentity_measurable environmentLaw))
      (completedEnvironmentKernel environmentLaw kernel) ∘ₘ environmentLaw.completion =
      coordinateStateKernel coordinate measurable kernel ∘ₘ environmentLaw := by
  have identity : coordinateStateKernel
      (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
      (measurable.comp (completedEnvironmentIdentity_measurable environmentLaw))
      (completedEnvironmentKernel environmentLaw kernel) =
      completedEnvironmentKernel environmentLaw (coordinateStateKernel coordinate measurable kernel) := by
    ext point subset measurableSubset
    simp only [coordinateStateKernel, completedEnvironmentKernel, Kernel.comap_apply,
      Kernel.prod_apply, Kernel.deterministic_apply]
  rw [identity, completedEnvironmentKernel_annealed_identity]

theorem completedEnvironment_coordinate_joint_probability_identity
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    annealedKernelProbability environmentLaw.completion
      (coordinateStateKernel (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
        (measurable.comp (completedEnvironmentIdentity_measurable environmentLaw))
        (completedEnvironmentKernel environmentLaw kernel)) =
      annealedKernelProbability environmentLaw (coordinateStateKernel coordinate measurable kernel) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact completedEnvironment_coordinate_joint_identity environmentLaw coordinate measurable kernel

/-- A measurable environmental observation is retained in its original
law, using the SAME completed-source limit kernel. No topology on the
environment or separability of the original state is required. -/
theorem coordinate_joint_weak_of_completed_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel (NullMeasurableSpace Environment environmentLaw) State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ environment ∂environmentLaw.completion,
      Tendsto (fun depth => conditionalKernelProbability
        (completedEnvironmentKernel environmentLaw (kernels depth)) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment))) :
    Tendsto (fun depth => annealedKernelProbability environmentLaw
      (coordinateStateKernel coordinate measurable (kernels depth))) atTop
      (𝓝 (annealedKernelProbability environmentLaw.completion
        (coordinateStateKernel (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
          (measurable.comp (completedEnvironmentIdentity_measurable environmentLaw)) limit))) := by
  have convergence := annealed_coordinate_joint_weak_of_quenched environmentLaw.completion
    (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
    (measurable.comp (completedEnvironmentIdentity_measurable environmentLaw))
    (fun depth => completedEnvironmentKernel environmentLaw (kernels depth)) limit quenched
  have finiteIdentity (depth : ℕ) := completedEnvironment_coordinate_joint_probability_identity
    environmentLaw coordinate measurable (kernels depth)
  simpa only [finiteIdentity] using convergence

theorem coordinate_original_joint_usual_tests_of_completed_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (coordinateMeasurable : Measurable coordinate)
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
    (test : Coordinate × OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ≥0) (bounded : ∀ point, ‖test point‖ ≤ bound)
    (usualContinuous : ∀ value, OriginalJointUsualSequentiallyContinuousTest
      (fun point => test (value, point))) :
    Tendsto (fun depth => ∫ point, test point ∂
      (coordinateStateKernel coordinate coordinateMeasurable (kernels depth) ∘ₘ environmentLaw)) atTop
      (𝓝 (∫ point, test point ∂
        (coordinateStateKernel (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
          (coordinateMeasurable.comp (completedEnvironmentIdentity_measurable environmentLaw)) limit ∘ₘ
            environmentLaw.completion))) := by
  have convergence := annealed_coordinate_original_joint_usual_tests_of_quenched environmentLaw.completion
    (fun point : NullMeasurableSpace Environment environmentLaw => coordinate point)
    (coordinateMeasurable.comp (completedEnvironmentIdentity_measurable environmentLaw))
    (fun depth => completedEnvironmentKernel environmentLaw (kernels depth)) limit quenched regular
    test measurable bound bounded usualContinuous
  have finiteIdentity (depth : ℕ) := completedEnvironment_coordinate_joint_identity
    environmentLaw coordinate coordinateMeasurable (kernels depth)
  simpa only [finiteIdentity] using convergence

end
end IGSIII34.Diffusion
