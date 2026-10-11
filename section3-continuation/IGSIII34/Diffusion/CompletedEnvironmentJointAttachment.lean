import IGSIII34.Diffusion.CompletedEnvironmentAnnealedExistence
import Mathlib.Probability.Kernel.Composition.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment Coordinate State : Type*} [MeasurableSpace Environment]
  [MetricSpace Coordinate] [SecondCountableTopology Coordinate]
  [MeasurableSpace Coordinate] [BorelSpace Coordinate]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

def coordinateStateKernel (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernel : Kernel Environment State) : Kernel Environment (Coordinate × State) :=
  Kernel.deterministic coordinate measurable ×ₖ kernel

instance coordinateStateKernel_markov (coordinate : Environment → Coordinate)
    (measurable : Measurable coordinate) (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    IsMarkovKernel (coordinateStateKernel coordinate measurable kernel) := by
  unfold coordinateStateKernel
  infer_instance

theorem coordinateStateKernel_probability
    (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] (sample : Environment) :
    conditionalKernelProbability (coordinateStateKernel coordinate measurable kernel) sample =
      (conditionalKernelProbability kernel sample).map
        (show Measurable (fun state : State => (coordinate sample, state)) from
          measurable_const.prodMk measurable_id).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (coordinateStateKernel coordinate measurable kernel) sample =
    (kernel sample).map (fun state => (coordinate sample, state))
  rw [coordinateStateKernel, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod]

/-- A measurable environmental coordinate is attached to the SAME
conditional state law. Its source sigma algebra can already be complete. -/
theorem annealed_coordinate_joint_weak_of_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (measurable : Measurable coordinate)
    (kernels : ℕ → Kernel Environment State) [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel Environment State) [IsMarkovKernel limit]
    (quenched : ∀ᵐ sample ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) sample) atTop
        (𝓝 (conditionalKernelProbability limit sample))) :
    Tendsto (fun depth => annealedKernelProbability environmentLaw
      (coordinateStateKernel coordinate measurable (kernels depth))) atTop
      (𝓝 (annealedKernelProbability environmentLaw (coordinateStateKernel coordinate measurable limit))) := by
  apply annealed_weak_of_quenched_measurable_environment
  filter_upwards [quenched] with sample convergence
  simp_rw [coordinateStateKernel_probability]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ convergence
    (continuous_const.prodMk continuous_id)

end
end IGSIII34.Diffusion
