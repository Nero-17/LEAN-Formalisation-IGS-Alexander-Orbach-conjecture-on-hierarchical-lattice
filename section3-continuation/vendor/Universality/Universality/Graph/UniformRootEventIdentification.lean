import Universality.Graph.UniformRootEventConvergence
import Universality.Graph.UniformRootProbabilitySpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- Almost sure eventual stabilization of measurable events implies convergence
of their actual probabilities. -/
theorem probability_event_tendsto_of_ae_eventually_iff {α : Type*} [MeasurableSpace α]
    (law : Measure α) [IsProbabilityMeasure law]
    (events : ℕ → Set α) (limitEvent : Set α)
    (hevents : ∀ n, MeasurableSet (events n)) (hlimit : MeasurableSet limitEvent)
    (hstabilize : ∀ᵐ sample ∂law, ∀ᶠ n in atTop, sample ∈ events n ↔ sample ∈ limitEvent) :
    Tendsto (fun n => law.real (events n)) atTop (𝓝 (law.real limitEvent)) := by
  classical
  have hintegral := tendsto_integral_of_dominated_convergence (μ := law)
    (fun _ => (1 : ℝ))
    (F := fun n => (events n).indicator (fun _ => (1 : ℝ)))
    (f := limitEvent.indicator (fun _ => (1 : ℝ)))
    (fun n => (measurable_const.indicator (hevents n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun sample => by
      simp only [Set.indicator_apply]
      split <;> norm_num)) (by
      filter_upwards [hstabilize] with sample hsample
      have heq : (fun n => (events n).indicator (fun _ => (1 : ℝ)) sample) =ᶠ[atTop]
          (fun _ => limitEvent.indicator (fun _ => (1 : ℝ)) sample) := by
        filter_upwards [hsample] with n hn
        simp only [Set.indicator_apply, hn]
      exact tendsto_const_nhds.congr' heq.symm)
  simpa only [integral_indicator_const (1 : ℝ) (hevents _),
    integral_indicator_const (1 : ℝ) hlimit, smul_eq_mul, mul_one] using hintegral

end
end Universality

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- Event convergence to the actual geometric-age mixture of infinite rooted
graphs, conditional only on the corresponding fixed-age event convergence. -/
theorem uniformVertexEventProbability_tendsto_sampleLaw (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : unitInterval)
    (limitEvent : Set rule.UniformRootSample) (hmeasurable : MeasurableSet limitEvent)
    (hlimit : ∀ age, Tendsto (fun n => (rule.ancestralSampleLaw age p).real
      (rule.ancestralStageEvent event age n)) atTop
        (𝓝 ((rule.ancestralSampleLaw age p).real {sample | ⟨age, sample⟩ ∈ limitEvent}))) :
    Tendsto (rule.uniformVertexEventProbability event (p : ℝ)) atTop
      (𝓝 ((rule.uniformRootSampleLaw hedges p).real limitEvent)) := by
  have hprobability : (rule.uniformRootSampleLaw hedges p).real limitEvent =
      ∑' age, (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1)) *
        (rule.ancestralSampleLaw age p).real {sample | ⟨age, sample⟩ ∈ limitEvent} := by
    unfold uniformRootSampleLaw
    rw [Universality.countableAgeMixture_real_apply _ _ hmeasurable]
    apply tsum_congr
    intro age
    rw [rule.rootAgeLaw_real_singleton]
    rfl
  rw [hprobability]
  exact rule.uniformVertexEventProbability_tendsto_mixture event hedges hvertices p
    (fun age => (rule.ancestralSampleLaw age p).real {sample | ⟨age, sample⟩ ∈ limitEvent}) hlimit


/-- The useful stabilization form: all probability convergence and age-tail
steps are discharged from almost sure finite-stage event stabilization. -/
theorem uniformVertexEventProbability_tendsto_of_ae_stabilize (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : unitInterval)
    (limitEvent : Set rule.UniformRootSample) (hmeasurable : MeasurableSet limitEvent)
    (hstabilize : ∀ age, ∀ᵐ sample ∂rule.ancestralSampleLaw age p,
      ∀ᶠ n in atTop, sample ∈ rule.ancestralStageEvent event age n ↔
        ⟨age, sample⟩ ∈ limitEvent) :
    Tendsto (rule.uniformVertexEventProbability event (p : ℝ)) atTop
      (𝓝 ((rule.uniformRootSampleLaw hedges p).real limitEvent)) := by
  apply rule.uniformVertexEventProbability_tendsto_sampleLaw event hedges hvertices p
    limitEvent hmeasurable
  intro age
  exact probability_event_tendsto_of_ae_eventually_iff (rule.ancestralSampleLaw age p)
    (rule.ancestralStageEvent event age) (Sigma.mk age ⁻¹' limitEvent)
    (rule.measurableSet_ancestralStageEvent event age)
    ((Universality.measurableSet_ageSample_iff limitEvent).mp hmeasurable age) (hstabilize age)

end
end Universality.Rule
