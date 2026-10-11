import IGSIII34.Diffusion.QuenchedKernelLimit
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Measure.NullMeasurable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped _root_.Topology BoundedContinuousFunction NNReal ENNReal

variable {Environment State : Type*} [MeasurableSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

def completedEnvironmentKernelProbability (kernel : Kernel Environment State)
    (markov : IsMarkovKernel kernel) (sample : Environment) : ProbabilityMeasure State :=
  ⟨kernel sample, markov.isProbabilityMeasure sample⟩

local instance : OpensMeasurableSpace State := inferInstance
local instance : TopologicalSpace (ProbabilityMeasure State) := inferInstance

/-- On a complete environmental probability space, a.e. weak convergence
of genuine finite kernels makes the ONE proposed limit law measurable.
No separability assumption on the full decorated state space is needed. -/
theorem complete_environment_weak_limit_measure_measurable
    (environmentLaw : Measure Environment) [environmentLaw.IsComplete]
    (kernels : ℕ → Kernel Environment State)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Environment → ProbabilityMeasure State)
    (convergence : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
        atTop (𝓝 (limit environment))) :
    Measurable (fun environment => (limit environment : Measure State)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {set : Set State | IsClosed set})
    (by rw [BorelSpace.measurable_eq (α := State), borel_eq_generateFrom_isClosed]) isPiSystem_isClosed
  intro closedSet isClosedSet
  let tests : ℕ → State →ᵇ ℝ := fun index =>
    BoundedContinuousFunction.comp (fun value : ℝ≥0 => (value : ℝ))
      NNReal.isometry_coe.lipschitz
      (thickenedIndicator (δ := (1 : ℝ) / (index + 1)) (by positivity) closedSet)
  have responseMeasurable (index : ℕ) :
      AEMeasurable (fun environment => ∫ point, tests index point
        ∂(limit environment : Measure State)) environmentLaw := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun depth environment => ∫ point, tests index point ∂kernels depth environment)
    · intro depth
      exact ((tests index).continuous.measurable.stronglyMeasurable.integral_kernel
        (κ := kernels depth)).aemeasurable
    · filter_upwards [convergence] with environment converges
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp converges (tests index)
  have realMeasurable : AEMeasurable (fun environment =>
      (limit environment : Measure State).real closedSet) environmentLaw := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop responseMeasurable
    apply Eventually.of_forall
    intro environment
    exact tendsto_integral_thickenedIndicator_of_isClosed
      (limit environment : Measure State) isClosedSet
      (δs := fun index => (1 : ℝ) / (index + 1)) (fun _ => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have measurableReal := aemeasurable_iff_measurable.mp realMeasurable
  have converted := ENNReal.measurable_ofReal.comp measurableReal
  convert converted using 1
  funext environment
  exact (ENNReal.ofReal_toReal (measure_ne_top (limit environment : Measure State) closedSet)).symm

theorem exists_complete_environment_quenched_limit_kernel
    (environmentLaw : Measure Environment) [environmentLaw.IsComplete]
    (kernels : ℕ → Kernel Environment State)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (existence : ∀ᵐ environment ∂environmentLaw,
      ∃ limit : ProbabilityMeasure State,
        Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
          atTop (𝓝 limit)) :
    ∃ kernel : Kernel Environment State, ∃ kernelMarkov : IsMarkovKernel kernel,
      ∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
          atTop (𝓝 (completedEnvironmentKernelProbability kernel kernelMarkov environment)) := by
  classical
  let limit (environment : Environment) : ProbabilityMeasure State :=
    if good : ∃ target : ProbabilityMeasure State,
        Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
          atTop (𝓝 target) then good.choose
    else completedEnvironmentKernelProbability (kernels 0) inferInstance environment
  have convergence : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => completedEnvironmentKernelProbability (kernels depth) inferInstance environment)
        atTop (𝓝 (limit environment)) := by
    filter_upwards [existence] with environment good
    simpa only [limit, dif_pos good] using good.choose_spec
  let kernel : Kernel Environment State :=
    ⟨fun environment => (limit environment : Measure State),
      complete_environment_weak_limit_measure_measurable environmentLaw kernels limit convergence⟩
  have markov : IsMarkovKernel kernel := ⟨fun environment => by
    change IsProbabilityMeasure (limit environment : Measure State)
    infer_instance⟩
  exact ⟨kernel, markov, convergence⟩

end
end IGSIII34.Diffusion
