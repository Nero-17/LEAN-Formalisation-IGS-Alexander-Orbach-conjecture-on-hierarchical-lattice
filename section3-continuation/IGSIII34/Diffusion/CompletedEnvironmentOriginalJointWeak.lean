import IGSIII34.Diffusion.CompletedEnvironmentOriginalJointIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment State : Type*} [environmentMeasurable : MeasurableSpace Environment]
  [MetricSpace Environment] [SecondCountableTopology Environment] [BorelSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

/-- The original environmental coordinate remains in the annealed joint
law, while only the source of the ONE limiting kernel is completed. -/
theorem original_environment_joint_weak_of_completed_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel (NullMeasurableSpace Environment environmentLaw) State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ environment ∂environmentLaw.completion,
      Tendsto (fun depth => conditionalKernelProbability
        (completedEnvironmentKernel environmentLaw (kernels depth)) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment))) :
    Tendsto (fun depth => jointKernelProbability environmentLaw (kernels depth)) atTop
      (𝓝 (annealedKernelProbability environmentLaw.completion
        (@coordinateStateKernel (NullMeasurableSpace Environment environmentLaw) Environment State
          inferInstance environmentMeasurable inferInstance (fun point => point)
          (completedEnvironmentIdentity_measurable environmentLaw) limit))) := by
  have convergence := @annealed_coordinate_joint_weak_of_quenched
    (NullMeasurableSpace Environment environmentLaw) Environment State
    inferInstance inferInstance inferInstance environmentMeasurable inferInstance
    inferInstance inferInstance inferInstance environmentLaw.completion inferInstance
    (fun point => point) (completedEnvironmentIdentity_measurable environmentLaw)
    (fun depth => completedEnvironmentKernel environmentLaw (kernels depth))
    inferInstance limit inferInstance quenched
  simpa only [completedEnvironment_original_joint_probability_identity] using convergence

end
end IGSIII34.Diffusion
