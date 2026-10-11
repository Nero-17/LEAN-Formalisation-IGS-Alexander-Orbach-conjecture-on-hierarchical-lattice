import IGSIII34.Diffusion.CompletedEnvironmentJointAttachment
import IGSIII34.Diffusion.CompletedEnvironmentKernelLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment State : Type*} [environmentMeasurable : MeasurableSpace Environment]
  [MetricSpace Environment] [SecondCountableTopology Environment] [BorelSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

/-- Completing only the source sigma algebra preserves the original
environment-state composition product exactly. -/
theorem completedEnvironment_original_joint_measure_identity
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    @coordinateStateKernel (NullMeasurableSpace Environment environmentLaw) Environment State inferInstance environmentMeasurable inferInstance (fun point : NullMeasurableSpace Environment environmentLaw =>
        (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw)
        (completedEnvironmentKernel environmentLaw kernel) ∘ₘ environmentLaw.completion =
      environmentLaw ⊗ₘ kernel := by
  have identity : @coordinateStateKernel (NullMeasurableSpace Environment environmentLaw) Environment State inferInstance environmentMeasurable inferInstance
      (fun point : NullMeasurableSpace Environment environmentLaw => (point : Environment))
      (completedEnvironmentIdentity_measurable environmentLaw)
      (completedEnvironmentKernel environmentLaw kernel) =
      completedEnvironmentKernel environmentLaw (Kernel.id ×ₖ kernel) := by
    ext point subset measurableSubset
    simp only [coordinateStateKernel, completedEnvironmentKernel, Kernel.comap_apply, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.id_apply]
  rw [identity, completedEnvironmentKernel_annealed_identity,
    ← Measure.compProd_eq_comp_prod]

theorem completedEnvironment_original_joint_probability_identity
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    annealedKernelProbability environmentLaw.completion
      (@coordinateStateKernel (NullMeasurableSpace Environment environmentLaw) Environment State inferInstance environmentMeasurable inferInstance (fun point : NullMeasurableSpace Environment environmentLaw =>
        (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw)
        (completedEnvironmentKernel environmentLaw kernel)) =
      jointKernelProbability environmentLaw kernel := by
  apply ProbabilityMeasure.toMeasure_injective
  exact completedEnvironment_original_joint_measure_identity environmentLaw kernel

end
end IGSIII34.Diffusion


