import IGSIII34.Diffusion.AnnealedGeneralPathIntegration
import Mathlib.Probability.Kernel.Composition.MeasureComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

variable {Environment State : Type*} [MeasurableSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

def annealedKernelProbability
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] : ProbabilityMeasure State :=
  ⟨kernel ∘ₘ environmentLaw, inferInstance⟩

/-- This integration requires only actual measurable kernels. In
particular it applies to a completed environmental sigma algebra and to
an arbitrary metric Borel target, without target separability. -/
theorem annealed_weak_of_quenched_measurable_environment
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment State) [∀ index, IsMarkovKernel (kernels index)]
    (limit : Kernel Environment State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ sample ∂environmentLaw,
      Tendsto (fun index => conditionalKernelProbability (kernels index) sample) atTop
        (𝓝 (conditionalKernelProbability limit sample))) :
    Tendsto (fun index => annealedKernelProbability environmentLaw (kernels index)) atTop
      (𝓝 (annealedKernelProbability environmentLaw limit)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have identity (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
      (∫ point, test point ∂(kernel ∘ₘ environmentLaw)) =
      ∫ sample, ∫ point, test point ∂kernel sample ∂environmentLaw := by
    exact ProbabilityTheory.Kernel.integral_comp (κ := Kernel.const Unit environmentLaw)
      (η := kernel) (a := ()) (test.integrable (μ := kernel ∘ₘ environmentLaw))
  change Tendsto (fun index => ∫ point, test point ∂(kernels index ∘ₘ environmentLaw)) atTop
    (𝓝 (∫ point, test point ∂(limit ∘ₘ environmentLaw)))
  simp_rw [identity]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro index
    exact (test.continuous.measurable.stronglyMeasurable.integral_kernel
      (κ := kernels index)).aestronglyMeasurable
  · exact integrable_const _
  · intro index
    exact Eventually.of_forall (fun sample => by
      simpa using (norm_integral_le_of_norm_le_const
        (μ := kernels index sample) (Eventually.of_forall test.norm_coe_le_norm)))
  · filter_upwards [quenched] with sample convergence
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence test

/-- The environmental sigma algebra may be larger than the Borel sigma
algebra, including its probability completion. All original environmental
information is retained in the actual composition-product probability. -/
theorem annealed_joint_weak_of_quenched_opens_measurable_environment
    [TopologicalSpace Environment] [SecondCountableTopology Environment]
    [OpensMeasurableSpace Environment]
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment State) [∀ index, IsMarkovKernel (kernels index)]
    (limit : Kernel Environment State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ sample ∂environmentLaw,
      Tendsto (fun index => conditionalKernelProbability (kernels index) sample) atTop
        (𝓝 (conditionalKernelProbability limit sample))) :
    Tendsto (fun index => jointKernelProbability environmentLaw (kernels index)) atTop
      (𝓝 (jointKernelProbability environmentLaw limit)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have finiteIdentity (index : ℕ) := Measure.integral_compProd
    (test.integrable (μ := environmentLaw ⊗ₘ kernels index))
  have limitIdentity := Measure.integral_compProd (test.integrable (μ := environmentLaw ⊗ₘ limit))
  change Tendsto (fun index => ∫ pair, test pair ∂(environmentLaw ⊗ₘ kernels index)) atTop
    (𝓝 (∫ pair, test pair ∂(environmentLaw ⊗ₘ limit)))
  simp_rw [finiteIdentity, limitIdentity]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro index
    exact (test.continuous.measurable.stronglyMeasurable.integral_kernel_prod_right'
      (κ := kernels index)).aestronglyMeasurable
  · exact integrable_const _
  · intro index
    exact Eventually.of_forall (fun sample => by
      simpa using (norm_integral_le_of_norm_le_const
        (μ := kernels index sample) (Eventually.of_forall (fun state => test.norm_coe_le_norm (sample, state)))))
  · filter_upwards [quenched] with sample convergence
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence
      (test.compContinuous ⟨fun state => (sample, state), continuous_const.prodMk continuous_id⟩)

end
end IGSIII34.Diffusion
