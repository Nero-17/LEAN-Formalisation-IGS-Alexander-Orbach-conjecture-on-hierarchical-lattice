import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

variable {Environment State : Type*}
  [TopologicalSpace Environment] [SecondCountableTopology Environment]
  [MeasurableSpace Environment] [BorelSpace Environment]
  [TopologicalSpace State] [SecondCountableTopology State]
  [MeasurableSpace State] [BorelSpace State]

def conditionalKernelProbability (kernel : Kernel Environment State) [IsMarkovKernel kernel]
    (sample : Environment) : ProbabilityMeasure State := ⟨kernel sample, inferInstance⟩

def jointKernelProbability (environment : Measure Environment) [IsProbabilityMeasure environment]
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] : ProbabilityMeasure (Environment × State) :=
  ⟨environment ⊗ₘ kernel, inferInstance⟩

/-- Integrating actual measurable conditional probabilities preserves weak
convergence jointly with the original environment. In particular, this
retains geometric and mass coordinates when they are part of `State`. -/
theorem annealed_joint_weak_of_quenched
    (environment : Measure Environment) [IsProbabilityMeasure environment]
    (kernels : ℕ → Kernel Environment State) [∀ index, IsMarkovKernel (kernels index)]
    (limit : Kernel Environment State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ sample ∂environment,
      Tendsto (fun index => conditionalKernelProbability (kernels index) sample)
        atTop (𝓝 (conditionalKernelProbability limit sample))) :
    Tendsto (fun index => jointKernelProbability environment (kernels index))
      atTop (𝓝 (jointKernelProbability environment limit)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have finiteIdentity (index : ℕ) := Measure.integral_compProd (test.integrable (μ := environment ⊗ₘ kernels index))
  have limitIdentity := Measure.integral_compProd (test.integrable (μ := environment ⊗ₘ limit))
  change Tendsto (fun index => ∫ pair, test pair ∂(environment ⊗ₘ kernels index)) atTop
    (𝓝 (∫ pair, test pair ∂(environment ⊗ₘ limit)))
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
