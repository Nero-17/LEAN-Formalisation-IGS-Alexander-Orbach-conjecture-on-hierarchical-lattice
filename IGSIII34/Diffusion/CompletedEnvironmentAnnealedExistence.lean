import IGSIII34.Diffusion.CompletedEnvironmentAnnealedWeak
import IGSIII34.Diffusion.CompletedEnvironmentQuenchedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment State : Type*} [MeasurableSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

def completedEnvironmentAnnealedLimitProbability
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernel : Kernel Environment State) (markov : IsMarkovKernel kernel) : ProbabilityMeasure State := by
  letI := markov
  exact annealedKernelProbability environmentLaw kernel

/-- A.e. existence of genuine original-state quenched weak limits on a
complete environment constructs ONE measurable probability kernel and
its genuine annealed weak limit, with no separability of the state space. -/
theorem exists_complete_environment_annealed_limit
    (environmentLaw : Measure Environment) [environmentLaw.IsComplete]
    [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (kernels depth)]
    (existence : ∀ᵐ environment ∂environmentLaw,
      ∃ limit : ProbabilityMeasure State,
        Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
          atTop (𝓝 limit)) :
    ∃ kernel : Kernel Environment State, ∃ markov : IsMarkovKernel kernel,
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
          atTop (𝓝 (completedEnvironmentKernelProbability kernel markov environment))) ∧
      Tendsto (fun depth => annealedKernelProbability environmentLaw (kernels depth)) atTop
        (𝓝 (completedEnvironmentAnnealedLimitProbability environmentLaw kernel markov)) := by
  obtain ⟨kernel, markov, quenched⟩ := exists_complete_environment_quenched_limit_kernel
    environmentLaw kernels existence
  letI := markov
  refine ⟨kernel, markov, quenched, ?_⟩
  exact annealed_weak_of_quenched_measurable_environment environmentLaw kernels kernel quenched

end
end IGSIII34.Diffusion
