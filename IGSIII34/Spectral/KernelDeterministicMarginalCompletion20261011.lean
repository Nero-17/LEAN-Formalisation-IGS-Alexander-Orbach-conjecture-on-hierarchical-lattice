import Mathlib.Probability.Kernel.Composition.Prod

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Input Space Target : Type*} [MeasurableSpace Input]
  [MeasurableSingletonClass Input] [MeasurableSpace Space] [MeasurableSpace Target]

theorem kernel_pair_eq_of_identity_marginal_completion20261011
    (kernel : Kernel Input Space) [IsMarkovKernel kernel]
    (first : Space → Input) (firstMeasurable : Measurable first)
    (second : Space → Target) (secondMeasurable : Measurable second)
    (firstIdentity : kernel.map first = Kernel.id) :
    kernel.map (fun value => (first value, second value)) = Kernel.id ×ₖ kernel.map second := by
  ext point : 1
  have fixed : (kernel point).map first = Measure.dirac point := by
    have equality := congrArg (fun output : Kernel Input Input => output point) firstIdentity
    simpa only [Kernel.map_apply _ firstMeasurable, Kernel.id_apply] using equality
  have firstAE : ∀ᵐ value ∂kernel point, first value = point := by
    apply (ae_map_iff firstMeasurable.aemeasurable (measurableSet_singleton point)).mp
    rw [fixed]
    simp
    rfl
  rw [Kernel.map_apply _ (firstMeasurable.prodMk secondMeasurable), Kernel.prod_apply,
    Kernel.id_apply, Kernel.map_apply _ secondMeasurable, Measure.dirac_prod,
    Measure.map_map measurable_prodMk_left secondMeasurable]
  apply Measure.map_congr
  filter_upwards [firstAE] with value equality
  simp only [Function.comp_apply, equality]

end
end IGSIII34.Spectral
