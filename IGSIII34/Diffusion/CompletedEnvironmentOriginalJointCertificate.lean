import IGSIII34.Diffusion.CompletedEnvironmentOriginalJointFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology NNReal

variable {Environment Index : Type*} [MeasurableSpace Environment]
  (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
  (kernels : Index → ℕ → Kernel Environment OriginalJointCompactSpace)
  [∀ index depth, IsMarkovKernel (kernels index depth)]

/-- A packaged, fully proved annealed family result. The limit kernel is
one object shared by all clocks in the family, including the usual-J1 tests. -/
structure CompletedOriginalJointAnnealedFamilyCertificate where
  kernel : Kernel (NullMeasurableSpace Environment environmentLaw) OriginalJointCompactSpace
  markov : IsMarkovKernel kernel
  regular : ∀ᵐ environment ∂environmentLaw.completion,
    OriginalJointUsualTestRegular (completedEnvironmentKernelProbability kernel markov environment)
  quenched : ∀ᵐ environment ∂environmentLaw.completion, ∀ index,
    Tendsto (fun depth => completedEnvironmentKernelProbability
      (completedEnvironmentKernel environmentLaw (kernels index depth)) inferInstance environment) atTop
      (𝓝 (completedEnvironmentKernelProbability kernel markov environment))
  annealed : ∀ index,
    Tendsto (fun depth => annealedKernelProbability environmentLaw (kernels index depth)) atTop
      (𝓝 (completedEnvironmentAnnealedLimitProbability environmentLaw.completion kernel markov))
  usualTests : ∀ index, ∀ test : OriginalJointCompactSpace → ℝ, Measurable test →
    ∀ bound : ℝ≥0, (∀ point, ‖test point‖ ≤ bound) →
      OriginalJointUsualSequentiallyContinuousTest test →
      Tendsto (fun depth => ∫ point, test point ∂(kernels index depth ∘ₘ environmentLaw)) atTop
        (𝓝 (∫ point, test point ∂(kernel ∘ₘ environmentLaw.completion)))

theorem exists_completed_original_joint_annealed_family_certificate
    (anchor : Index)
    (actual : ∀ᵐ environment ∂environmentLaw,
      ∃ target : ProbabilityMeasure OriginalJointCompactSpace,
        OriginalJointUsualTestRegular target ∧ ∀ index,
          Tendsto (fun depth => completedEnvironmentKernelProbability
            (kernels index depth) inferInstance environment) atTop (𝓝 target)) :
    Nonempty (CompletedOriginalJointAnnealedFamilyCertificate environmentLaw kernels) := by
  obtain ⟨kernel, markov, regular, quenched, conclusions⟩ :=
    exists_completed_original_joint_annealed_family environmentLaw anchor kernels actual
  exact ⟨⟨kernel, markov, regular, quenched,
    fun index => (conclusions index).1, fun index => (conclusions index).2⟩⟩

end
end IGSIII34.Diffusion
