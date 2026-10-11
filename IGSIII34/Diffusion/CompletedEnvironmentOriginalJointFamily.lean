import IGSIII34.Diffusion.CompletedEnvironmentAnnealedFamily
import IGSIII34.Diffusion.CompletedEnvironmentKernelLift
import IGSIII34.Diffusion.OriginalJointAnnealedUsualTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Environment Index : Type*} [MeasurableSpace Environment]

/-- A genuine common quenched limit with continuous-sample regularity gives
one completed-environment kernel for the whole family. Its finite annealed
laws are exactly the original, uncompleted environmental mixtures. -/
theorem exists_completed_original_joint_annealed_family
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (anchor : Index) (kernels : Index → ℕ → Kernel Environment OriginalJointCompactSpace)
    [∀ index depth, IsMarkovKernel (kernels index depth)]
    (actual : ∀ᵐ environment ∂environmentLaw,
      ∃ target : ProbabilityMeasure OriginalJointCompactSpace,
        OriginalJointUsualTestRegular target ∧ ∀ index,
          Tendsto (fun depth => completedEnvironmentKernelProbability
            (kernels index depth) inferInstance environment) atTop (𝓝 target)) :
    ∃ kernel : Kernel (NullMeasurableSpace Environment environmentLaw) OriginalJointCompactSpace,
      ∃ markov : IsMarkovKernel kernel,
        (∀ᵐ environment ∂environmentLaw.completion,
          OriginalJointUsualTestRegular (completedEnvironmentKernelProbability kernel markov environment)) ∧
        (∀ᵐ environment ∂environmentLaw.completion, ∀ index,
          Tendsto (fun depth => completedEnvironmentKernelProbability
            (completedEnvironmentKernel environmentLaw (kernels index depth)) inferInstance environment)
            atTop (𝓝 (completedEnvironmentKernelProbability kernel markov environment))) ∧
        ∀ index,
          Tendsto (fun depth => annealedKernelProbability environmentLaw (kernels index depth)) atTop
            (𝓝 (completedEnvironmentAnnealedLimitProbability environmentLaw.completion kernel markov)) ∧
          ∀ test : OriginalJointCompactSpace → ℝ, Measurable test →
            ∀ bound : ℝ≥0, (∀ point, ‖test point‖ ≤ bound) →
              OriginalJointUsualSequentiallyContinuousTest test →
              Tendsto (fun depth => ∫ point, test point ∂(kernels index depth ∘ₘ environmentLaw)) atTop
                (𝓝 (∫ point, test point ∂(kernel ∘ₘ environmentLaw.completion))) := by
  have existence : ∀ᵐ environment ∂environmentLaw.completion,
      ∃ target : ProbabilityMeasure OriginalJointCompactSpace, ∀ index,
        Tendsto (fun depth => completedEnvironmentKernelProbability
          (completedEnvironmentKernel environmentLaw (kernels index depth)) inferInstance environment)
          atTop (𝓝 target) := by
    change ∀ᵐ environment ∂environmentLaw, _
    filter_upwards [actual] with environment witness
    exact ⟨witness.choose, witness.choose_spec.2⟩
  obtain ⟨kernel, markov, quenched, annealed⟩ :=
    exists_complete_environment_common_annealed_limit environmentLaw.completion anchor
      (fun index depth => completedEnvironmentKernel environmentLaw (kernels index depth)) existence
  letI := markov
  have regular : ∀ᵐ environment ∂environmentLaw.completion,
      OriginalJointUsualTestRegular (completedEnvironmentKernelProbability kernel markov environment) := by
    apply originalJoint_selected_kernel_usual_regular environmentLaw.completion
      (fun depth => completedEnvironmentKernel environmentLaw (kernels anchor depth)) kernel
      (quenched.mono (fun _ converges => converges anchor))
    change ∀ᵐ environment ∂environmentLaw, _
    filter_upwards [actual] with environment witness
    exact ⟨witness.choose, witness.choose_spec.2 anchor, witness.choose_spec.1⟩
  refine ⟨kernel, markov, regular, quenched, ?_⟩
  intro index
  refine ⟨?_, ?_⟩
  · simpa only [completedEnvironmentKernel_probability_identity] using annealed index
  · intro test measurable bound bounded usualContinuous
    have convergence := annealed_original_joint_usual_tests_of_quenched environmentLaw.completion
      (fun depth => completedEnvironmentKernel environmentLaw (kernels index depth)) kernel
      (quenched.mono (fun _ converges => converges index)) regular test measurable bound bounded usualContinuous
    simpa only [completedEnvironmentKernel_annealed_identity] using convergence

end
end IGSIII34.Diffusion
