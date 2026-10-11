import IGSIII34.Diffusion.QuenchedKernelLimit
import IGSIII34.Diffusion.AnnealedWeakIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped _root_.Topology

variable {Environment Code : Type*} [MeasurableSpace Environment]
  [TopologicalSpace Code] [PseudoMetrizableSpace Code] [SeparableSpace Code]
  [MeasurableSpace Code] [BorelSpace Code]

/-- Mere a.e. existence of quenched weak limits suffices to construct an
everywhere measurable probability kernel. The preliminary choice of limits
is not required to be measurable. -/
theorem exists_quenched_limit_markov_kernel_of_ae_existence
    (environmentLaw : Measure Environment)
    (sequence : ℕ → Environment → ProbabilityMeasure Code)
    (sequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (sequence depth))
    (existence : ∀ᵐ environment ∂environmentLaw, ∃ limit : ProbabilityMeasure Code,
      Tendsto (fun depth => sequence depth environment) atTop (𝓝 limit)) :
    ∃ kernel : Kernel Environment Code, ∃ kernelMarkov : IsMarkovKernel kernel,
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => sequence depth environment) atTop
          (𝓝 (⟨kernel environment, kernelMarkov.isProbabilityMeasure environment⟩ :
            ProbabilityMeasure Code))) := by
  classical
  let limit : Environment → ProbabilityMeasure Code := fun environment =>
    if converges : ∃ limit : ProbabilityMeasure Code,
        Tendsto (fun depth => sequence depth environment) atTop (𝓝 limit)
      then converges.choose else sequence 0 environment
  have convergence : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => sequence depth environment) atTop (𝓝 (limit environment)) := by
    filter_upwards [existence] with environment converges
    simpa only [limit, dif_pos converges] using converges.choose_spec
  obtain ⟨kernel, kernelMarkov, _, convergence⟩ :=
    exists_quenched_limit_markov_kernel environmentLaw sequence sequenceMeasurable limit convergence
  exact ⟨kernel, kernelMarkov, convergence⟩

variable [TopologicalSpace Environment] [SecondCountableTopology Environment]
  [BorelSpace Environment] [SecondCountableTopology Code]

/-- Actual finite measurable conditional laws and a.e. existence of their
quenched weak limit produce a genuine annealed joint weak limit, retaining
the original environment coordinate. -/
theorem exists_annealed_joint_limit_of_quenched_existence
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment Code) [∀ depth, IsMarkovKernel (kernels depth)]
    (sequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (conditionalKernelProbability (kernels depth)))
    (existence : ∀ᵐ environment ∂environmentLaw, ∃ limit : ProbabilityMeasure Code,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment)
        atTop (𝓝 limit)) :
    ∃ kernel : Kernel Environment Code, ∃ kernelMarkov : IsMarkovKernel kernel,
      letI : IsMarkovKernel kernel := kernelMarkov;
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment)
          atTop (𝓝 (conditionalKernelProbability kernel environment))) ∧
      Tendsto (fun depth => jointKernelProbability environmentLaw (kernels depth))
        atTop (𝓝 (jointKernelProbability environmentLaw kernel)) := by
  obtain ⟨kernel, kernelMarkov, convergence⟩ :=
    exists_quenched_limit_markov_kernel_of_ae_existence environmentLaw
      (fun depth => conditionalKernelProbability (kernels depth)) sequenceMeasurable existence
  letI : IsMarkovKernel kernel := kernelMarkov
  refine ⟨kernel, kernelMarkov, convergence, ?_⟩
  exact annealed_joint_weak_of_quenched environmentLaw kernels kernel convergence

end
end IGSIII34.Diffusion
