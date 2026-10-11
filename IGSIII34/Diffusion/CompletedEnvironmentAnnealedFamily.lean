import IGSIII34.Diffusion.CompletedEnvironmentAnnealedExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology

variable {Environment State Index : Type*} [MeasurableSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

/-- A common quenched limit for several genuine finite kernels gives ONE
measurable limit kernel shared by the whole family. Selection uses the common
existence statement, so no uniqueness or separability theorem is assumed. -/
theorem exists_complete_environment_common_annealed_limit
    (environmentLaw : Measure Environment) [environmentLaw.IsComplete]
    [IsProbabilityMeasure environmentLaw]
    (anchor : Index) (kernels : Index → ℕ → Kernel Environment State)
    [∀ index depth, IsMarkovKernel (kernels index depth)]
    (existence : ∀ᵐ environment ∂environmentLaw,
      ∃ limit : ProbabilityMeasure State, ∀ index,
        Tendsto (fun depth => completedEnvironmentKernelProbability
          (kernels index depth) inferInstance environment) atTop (𝓝 limit)) :
    ∃ kernel : Kernel Environment State, ∃ markov : IsMarkovKernel kernel,
      (∀ᵐ environment ∂environmentLaw, ∀ index,
        Tendsto (fun depth => completedEnvironmentKernelProbability
          (kernels index depth) inferInstance environment) atTop
          (𝓝 (completedEnvironmentKernelProbability kernel markov environment))) ∧
      ∀ index, Tendsto (fun depth => annealedKernelProbability environmentLaw (kernels index depth))
        atTop (𝓝 (completedEnvironmentAnnealedLimitProbability environmentLaw kernel markov)) := by
  classical
  let limit (environment : Environment) : ProbabilityMeasure State :=
    if good : ∃ target : ProbabilityMeasure State, ∀ index,
        Tendsto (fun depth => completedEnvironmentKernelProbability
          (kernels index depth) inferInstance environment) atTop (𝓝 target)
    then good.choose
    else completedEnvironmentKernelProbability (kernels anchor 0) inferInstance environment
  have convergence : ∀ᵐ environment ∂environmentLaw, ∀ index,
      Tendsto (fun depth => completedEnvironmentKernelProbability
        (kernels index depth) inferInstance environment) atTop (𝓝 (limit environment)) := by
    filter_upwards [existence] with environment good
    simpa only [limit, dif_pos good] using good.choose_spec
  let kernel : Kernel Environment State :=
    ⟨fun environment => (limit environment : Measure State),
      complete_environment_weak_limit_measure_measurable environmentLaw (kernels anchor) limit
        (convergence.mono (fun _ converges => converges anchor))⟩
  have markov : IsMarkovKernel kernel := ⟨fun environment => by
    change IsProbabilityMeasure (limit environment : Measure State)
    infer_instance⟩
  letI := markov
  refine ⟨kernel, markov, convergence, ?_⟩
  intro index
  exact annealed_weak_of_quenched_measurable_environment environmentLaw (kernels index) kernel
    (convergence.mono (fun _ converges => converges index))

end
end IGSIII34.Diffusion
