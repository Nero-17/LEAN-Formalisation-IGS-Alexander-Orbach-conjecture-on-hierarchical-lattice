import IGSIII34.Diffusion.CompletedEnvironmentAnnealedWeak
import IGSIII34.Diffusion.CompletedEnvironmentQuenchedKernel
import Mathlib.Probability.Kernel.Composition.CompMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Environment State : Type*} [environmentMeasurable : MeasurableSpace Environment]
  [MetricSpace State] [MeasurableSpace State] [BorelSpace State]

theorem completedEnvironmentIdentity_measurable (environmentLaw : Measure Environment) :
    @Measurable (NullMeasurableSpace Environment environmentLaw) Environment
      inferInstance environmentMeasurable (fun point => point) := by
  intro subset measurableSubset
  exact measurableSubset.nullMeasurableSet (μ := environmentLaw)

def completedEnvironmentKernel (environmentLaw : Measure Environment)
    (kernel : Kernel Environment State) : Kernel (NullMeasurableSpace Environment environmentLaw) State :=
  kernel.comap (fun point => (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw)

instance completedEnvironmentKernel_markov (environmentLaw : Measure Environment)
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    IsMarkovKernel (completedEnvironmentKernel environmentLaw kernel) := by
  unfold completedEnvironmentKernel
  infer_instance

theorem completedEnvironmentIdentity_map (environmentLaw : Measure Environment) :
    @Measure.map (NullMeasurableSpace Environment environmentLaw) Environment inferInstance environmentMeasurable
      (fun point => point) environmentLaw.completion = environmentLaw := by
  ext subset measurableSubset
  rw [Measure.map_apply (completedEnvironmentIdentity_measurable environmentLaw) measurableSubset]
  rfl

instance completedEnvironmentLaw_probability (environmentLaw : Measure Environment)
    [IsProbabilityMeasure environmentLaw] : IsProbabilityMeasure environmentLaw.completion :=
  ⟨by simpa only [Measure.completion_apply] using measure_univ (μ := environmentLaw)⟩

/-- Completing the environmental sigma algebra leaves the actual
annealed state law unchanged, rather than replacing it with a new law. -/
theorem completedEnvironmentKernel_annealed_identity
    (environmentLaw : Measure Environment) (kernel : Kernel Environment State) :
    completedEnvironmentKernel environmentLaw kernel ∘ₘ environmentLaw.completion =
      kernel ∘ₘ environmentLaw := by
  calc
    _ = (kernel ∘ₖ Kernel.deterministic (fun point : NullMeasurableSpace Environment environmentLaw =>
          (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw)) ∘ₘ environmentLaw.completion := by
      rw [Kernel.comp_deterministic_eq_comap]
      rfl
    _ = kernel ∘ₘ (Kernel.deterministic (fun point : NullMeasurableSpace Environment environmentLaw =>
          (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw) ∘ₘ environmentLaw.completion) :=
      Measure.comp_assoc.symm
    _ = kernel ∘ₘ environmentLaw := by
      have deterministicIdentity :
          @Measure.bind (NullMeasurableSpace Environment environmentLaw) Environment
            inferInstance environmentMeasurable environmentLaw.completion
            (Kernel.deterministic (fun point : NullMeasurableSpace Environment environmentLaw =>
              (point : Environment)) (completedEnvironmentIdentity_measurable environmentLaw)) = environmentLaw :=
        (Measure.deterministic_comp_eq_map (completedEnvironmentIdentity_measurable environmentLaw)).trans
          (completedEnvironmentIdentity_map environmentLaw)
      exact congrArg (fun measure : @Measure Environment environmentMeasurable =>
        @Measure.bind Environment State environmentMeasurable inferInstance measure kernel) deterministicIdentity

theorem completedEnvironmentKernel_probability_identity
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (kernel : Kernel Environment State) [IsMarkovKernel kernel] :
    annealedKernelProbability environmentLaw.completion (completedEnvironmentKernel environmentLaw kernel) =
      annealedKernelProbability environmentLaw kernel := by
  apply ProbabilityMeasure.toMeasure_injective
  exact completedEnvironmentKernel_annealed_identity environmentLaw kernel

end
end IGSIII34.Diffusion
