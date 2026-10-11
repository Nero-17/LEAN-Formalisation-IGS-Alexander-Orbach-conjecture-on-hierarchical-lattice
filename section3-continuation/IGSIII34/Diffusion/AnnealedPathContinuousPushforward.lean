import IGSIII34.Diffusion.AnnealedGeneralPathIntegration
import Mathlib.Probability.Kernel.Composition.MapComap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment State Target : Type*}
  [MeasurableSpace Environment]
  [TopologicalSpace State] [MeasurableSpace State] [BorelSpace State]
  [TopologicalSpace Target] [MeasurableSpace Target] [BorelSpace Target]

theorem conditionalKernelProbability_continuous_map
    (kernel : Kernel Environment State) [IsMarkovKernel kernel]
    (carrier : State → Target) (continuous : Continuous carrier) (environment : Environment) :
    letI : IsMarkovKernel (kernel.map carrier) := Kernel.IsMarkovKernel.map kernel continuous.measurable;
    conditionalKernelProbability (kernel.map carrier) environment =
      (conditionalKernelProbability kernel environment).map continuous.measurable.aemeasurable := by
  letI : IsMarkovKernel (kernel.map carrier) := Kernel.IsMarkovKernel.map kernel continuous.measurable
  apply Subtype.ext
  exact Kernel.map_apply kernel continuous.measurable environment

variable [TopologicalSpace Environment] [SecondCountableTopology Environment] [BorelSpace Environment]

/-- A continuous carrier changes neither the selected limiting kernel nor
its underlying process: the target kernel is exactly the map of the same
kernel. This applies to integer-J1 to genuine usual-local-J1 transport. -/
theorem annealed_joint_weak_continuous_pushforward
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel Environment State) [IsMarkovKernel limit]
    (carrier : State → Target) (continuous : Continuous carrier)
    (quenched : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment))) :
    letI : ∀ depth, IsMarkovKernel ((kernels depth).map carrier) :=
      fun depth => Kernel.IsMarkovKernel.map (kernels depth) continuous.measurable;
    letI : IsMarkovKernel (limit.map carrier) := Kernel.IsMarkovKernel.map limit continuous.measurable;
    (∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability ((kernels depth).map carrier) environment) atTop
        (𝓝 (conditionalKernelProbability (limit.map carrier) environment))) ∧
    Tendsto (fun depth => jointKernelProbability environmentLaw ((kernels depth).map carrier)) atTop
      (𝓝 (jointKernelProbability environmentLaw (limit.map carrier))) := by
  letI : ∀ depth, IsMarkovKernel ((kernels depth).map carrier) :=
    fun depth => Kernel.IsMarkovKernel.map (kernels depth) continuous.measurable
  letI : IsMarkovKernel (limit.map carrier) := Kernel.IsMarkovKernel.map limit continuous.measurable
  have mappedWeak : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability ((kernels depth).map carrier) environment) atTop
        (𝓝 (conditionalKernelProbability (limit.map carrier) environment)) := by
    filter_upwards [quenched] with environment weak
    have finiteEquality (depth : ℕ) :
        conditionalKernelProbability ((kernels depth).map carrier) environment =
          (conditionalKernelProbability (kernels depth) environment).map continuous.measurable.aemeasurable :=
      conditionalKernelProbability_continuous_map (kernels depth) carrier continuous environment
    have limitEquality : conditionalKernelProbability (limit.map carrier) environment =
        (conditionalKernelProbability limit environment).map continuous.measurable.aemeasurable :=
      conditionalKernelProbability_continuous_map limit carrier continuous environment
    simp_rw [finiteEquality, limitEquality]
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun depth => conditionalKernelProbability (kernels depth) environment)
      (conditionalKernelProbability limit environment) weak continuous
  exact ⟨mappedWeak, annealed_joint_weak_of_quenched_general environmentLaw
    (fun depth => (kernels depth).map carrier) (limit.map carrier) mappedWeak⟩

end
end IGSIII34.Diffusion
