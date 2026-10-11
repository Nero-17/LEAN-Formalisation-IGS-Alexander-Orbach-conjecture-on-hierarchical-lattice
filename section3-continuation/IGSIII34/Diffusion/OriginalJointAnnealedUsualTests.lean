import IGSIII34.Diffusion.OriginalJointContinuousSampleLaw
import IGSIII34.Diffusion.CompletedEnvironmentAnnealedWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Environment : Type*} [MeasurableSpace Environment]

/-- Uniqueness identifies the selected measurable kernel with the actual
continuous-sample target, rather than assuming regularity of the choice. -/
theorem originalJoint_selected_kernel_usual_regular
    (environmentLaw : Measure Environment)
    (kernels : ℕ → Kernel Environment OriginalJointCompactSpace)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel limit]
    (selected : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment)))
    (actual : ∀ᵐ environment ∂environmentLaw,
      ∃ law : ProbabilityMeasure OriginalJointCompactSpace,
        Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment) atTop (𝓝 law) ∧
          OriginalJointUsualTestRegular law) :
    ∀ᵐ environment ∂environmentLaw,
      OriginalJointUsualTestRegular (conditionalKernelProbability limit environment) := by
  filter_upwards [selected, actual] with environment convergence witness
  obtain ⟨law, actualConvergence, regular⟩ := witness
  have identity := tendsto_nhds_unique convergence actualConvergence
  rw [identity]
  exact regular

/-- Actual measurable original-state kernels and the SAME selected
limit kernel satisfy bounded measurable usual-J1 test convergence. -/
theorem annealed_original_joint_usual_tests_of_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment OriginalJointCompactSpace)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel limit]
    (quenched : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment)))
    (regular : ∀ᵐ environment ∂environmentLaw,
      OriginalJointUsualTestRegular (conditionalKernelProbability limit environment))
    (test : OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ≥0) (bounded : ∀ point, ‖test point‖ ≤ bound)
    (usualContinuous : OriginalJointUsualSequentiallyContinuousTest test) :
    Tendsto (fun depth => ∫ point, test point ∂(kernels depth ∘ₘ environmentLaw)) atTop
      (𝓝 (∫ point, test point ∂(limit ∘ₘ environmentLaw))) := by
  have integrable (kernel : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel kernel] :
      Integrable test (kernel ∘ₘ environmentLaw) :=
    (integrable_const (bound : ℝ)).mono' measurable.aestronglyMeasurable
      (Eventually.of_forall bounded)
  have identity (kernel : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel kernel] :
      (∫ point, test point ∂(kernel ∘ₘ environmentLaw)) =
        ∫ environment, ∫ point, test point ∂kernel environment ∂environmentLaw :=
    ProbabilityTheory.Kernel.integral_comp (κ := Kernel.const Unit environmentLaw)
      (η := kernel) (a := ()) (integrable kernel)
  simp_rw [identity]
  apply tendsto_integral_of_dominated_convergence (fun _ => (bound : ℝ))
  · intro depth
    exact (measurable.stronglyMeasurable.integral_kernel (κ := kernels depth)).aestronglyMeasurable
  · exact integrable_const _
  · intro depth
    exact Eventually.of_forall (fun environment => by
      simpa using norm_integral_le_of_norm_le_const (μ := kernels depth environment) (Eventually.of_forall bounded))
  · filter_upwards [quenched, regular] with environment convergence testRegular
    exact probability_weak_integral_bounded_ae_continuous _ _ convergence test measurable bound
      (fun point => by simpa only [Real.norm_eq_abs] using bounded point)
      (testRegular test usualContinuous)

end
end IGSIII34.Diffusion


