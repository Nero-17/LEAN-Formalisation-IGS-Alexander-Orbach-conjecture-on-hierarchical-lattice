import IGSIII34.Diffusion.QuenchedKernelExistence
import IGSIII34.Diffusion.AnnealedGeneralPathIntegration
import Mathlib.Probability.Kernel.Composition.MapComap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology

variable {Environment Code State : Type*} [MeasurableSpace Environment]
  [TopologicalSpace Code] [PseudoMetrizableSpace Code] [SeparableSpace Code]
  [MeasurableSpace Code] [BorelSpace Code]
  [TopologicalSpace State] [MeasurableSpace State] [BorelSpace State]

/-- A measurable reconstruction of the continuous limiting paths suffices
to construct their full-path kernel. Full-path weak convergence is an
independent conclusion in the a.e. existence input; it is never replaced
by convergence of countable observations. The state need not be separable. -/
theorem exists_reconstructed_quenched_markov_kernel
    (environmentLaw : Measure Environment)
    (codeSequence : ℕ → Environment → ProbabilityMeasure Code)
    (codeSequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (codeSequence depth))
    (stateSequence : ℕ → Environment → ProbabilityMeasure State)
    (reconstruct : Code → State) (reconstructMeasurable : Measurable reconstruct)
    (existence : ∀ᵐ environment ∂environmentLaw, ∃ limit : ProbabilityMeasure Code,
      Tendsto (fun depth => codeSequence depth environment) atTop (𝓝 limit) ∧
      Tendsto (fun depth => stateSequence depth environment) atTop
        (𝓝 (limit.map reconstructMeasurable.aemeasurable))) :
    ∃ kernel : Kernel Environment State, ∃ kernelMarkov : IsMarkovKernel kernel,
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => stateSequence depth environment) atTop
          (𝓝 (⟨kernel environment, kernelMarkov.isProbabilityMeasure environment⟩ :
            ProbabilityMeasure State))) := by
  classical
  let chosen : Environment → ProbabilityMeasure Code := fun environment =>
    if good : ∃ limit : ProbabilityMeasure Code,
        Tendsto (fun depth => codeSequence depth environment) atTop (𝓝 limit) ∧
        Tendsto (fun depth => stateSequence depth environment) atTop
          (𝓝 (limit.map reconstructMeasurable.aemeasurable))
      then good.choose else codeSequence 0 environment
  have codeWeak : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => codeSequence depth environment) atTop (𝓝 (chosen environment)) := by
    filter_upwards [existence] with environment good
    simpa only [chosen, dif_pos good] using good.choose_spec.1
  have stateWeak : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => stateSequence depth environment) atTop
        (𝓝 ((chosen environment).map reconstructMeasurable.aemeasurable)) := by
    filter_upwards [existence] with environment good
    simpa only [chosen, dif_pos good] using good.choose_spec.2
  obtain ⟨codeKernel, codeMarkov, codeEquality, _⟩ :=
    exists_quenched_limit_markov_kernel environmentLaw codeSequence
      codeSequenceMeasurable chosen codeWeak
  letI : IsMarkovKernel codeKernel := codeMarkov
  let kernel := codeKernel.map reconstruct
  have kernelMarkov : IsMarkovKernel kernel := Kernel.IsMarkovKernel.map codeKernel reconstructMeasurable
  refine ⟨kernel, kernelMarkov, ?_⟩
  filter_upwards [stateWeak, codeEquality] with environment weak equality
  have probabilityEquality :
      (⟨kernel environment, kernelMarkov.isProbabilityMeasure environment⟩ : ProbabilityMeasure State) =
        (chosen environment).map reconstructMeasurable.aemeasurable := by
    apply Subtype.ext
    change kernel environment = ((chosen environment : ProbabilityMeasure Code) : Measure Code).map reconstruct
    rw [Kernel.map_apply codeKernel reconstructMeasurable, equality]
  rwa [probabilityEquality]

variable [TopologicalSpace Environment] [SecondCountableTopology Environment] [BorelSpace Environment]

/-- The reconstructed full-path Markov kernel integrates to a genuine joint
environment/full-state weak limit, without a second-countability assumption
on the full-path topology. -/
theorem exists_annealed_reconstructed_joint_limit
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (codeSequence : ℕ → Environment → ProbabilityMeasure Code)
    (codeSequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (codeSequence depth))
    (stateKernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (stateKernels depth)]
    (reconstruct : Code → State) (reconstructMeasurable : Measurable reconstruct)
    (existence : ∀ᵐ environment ∂environmentLaw, ∃ limit : ProbabilityMeasure Code,
      Tendsto (fun depth => codeSequence depth environment) atTop (𝓝 limit) ∧
      Tendsto (fun depth => conditionalKernelProbability (stateKernels depth) environment) atTop
        (𝓝 (limit.map reconstructMeasurable.aemeasurable))) :
    ∃ kernel : Kernel Environment State, ∃ kernelMarkov : IsMarkovKernel kernel,
      letI : IsMarkovKernel kernel := kernelMarkov;
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => conditionalKernelProbability (stateKernels depth) environment) atTop
          (𝓝 (conditionalKernelProbability kernel environment))) ∧
      Tendsto (fun depth => jointKernelProbability environmentLaw (stateKernels depth)) atTop
        (𝓝 (jointKernelProbability environmentLaw kernel)) := by
  obtain ⟨kernel, kernelMarkov, weak⟩ := exists_reconstructed_quenched_markov_kernel
    environmentLaw codeSequence codeSequenceMeasurable
    (fun depth => conditionalKernelProbability (stateKernels depth)) reconstruct reconstructMeasurable existence
  letI : IsMarkovKernel kernel := kernelMarkov
  exact ⟨kernel, kernelMarkov, weak,
    annealed_joint_weak_of_quenched_general environmentLaw stateKernels kernel weak⟩

end
end IGSIII34.Diffusion
