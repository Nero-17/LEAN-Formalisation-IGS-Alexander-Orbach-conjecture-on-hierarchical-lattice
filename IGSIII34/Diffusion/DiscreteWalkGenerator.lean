import IGSIII34.Diffusion.ActualDiscreteWalkProperties
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finiteWalkKernel_integral (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (first : Vertex) :
    ∫ last, potential last ∂finiteWalkKernel endpoint positiveDegree first =
      transition endpoint potential first := by
  rw [integral_fintype Integrable.of_finite, transition_eq_kernel endpoint positiveDegree]
  apply Finset.sum_congr rfl
  intro last _
  simp only [measureReal_def, finiteWalkKernel_singleton,
    ENNReal.toReal_ofReal (transitionKernel_nonnegative endpoint first last), smul_eq_mul]

/-- The constructed trajectory law satisfies the actual finite graph
transition operator as a conditional expectation given its entire past. -/
theorem finiteDiscreteWalkLaw_conditional_expectation [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => potential (path (time + 1)) | MeasurableSpace.comap (frestrictLe time) inferInstance] =ᵐ[
        finiteDiscreteWalkLaw endpoint positiveDegree initial]
      fun path => transition endpoint potential (path time) := by
  have potentialMeasurable : StronglyMeasurable potential :=
    (measurable_of_countable potential).stronglyMeasurable
  have potentialIntegrable : Integrable potential
      ((finiteDiscreteWalkLaw endpoint positiveDegree initial).map (fun path => path (time + 1))) :=
    Integrable.of_finite
  have conditional := condExp_ae_eq_integral_condDistrib (measurable_frestrictLe time)
    (measurable_pi_apply (time + 1)).aemeasurable potentialMeasurable
    (potentialIntegrable.comp_aemeasurable (measurable_pi_apply (time + 1)).aemeasurable)
  have kernelEquality := ae_of_ae_map (measurable_frestrictLe time).aemeasurable
    (finiteDiscreteWalkLaw_condDistrib endpoint positiveDegree initial time)
  filter_upwards [conditional, kernelEquality] with path conditionalEquality equality
  rw [conditionalEquality, equality]
  exact finiteWalkKernel_integral endpoint positiveDegree potential (path time)

theorem actualFiniteDiscreteWalkLaw_conditional_expectation (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (potential : ActualFiniteCluster rule configuration scale scalePositive depth → ℝ) (time : ℕ) :
    (actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial)[
      fun path => potential (path (time + 1)) | MeasurableSpace.comap (frestrictLe time) inferInstance] =ᵐ[
        actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial]
      fun path => potential (path time) +
        rateOneGenerator (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
          potential (path time) :=
  finiteDiscreteWalkLaw_conditional_expectation _ _ _ potential time

end
end IGSIII34.Diffusion
