import Universality.Graph.FiniteAgeDisintegration

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

variable (rule : Rule)
variable (event : ∀ depth, Fin (rule.generation depth).vertices →
  FiniteNetwork.Configuration (rule.generation depth).edges → Prop)

def uniformVertexEventProbability (p : ℝ) (depth : ℕ) : ℝ :=
  (∑ configuration, FiniteNetwork.bernoulliWeight p configuration *
    ∑ vertex, if event depth vertex configuration then (1 : ℝ) else 0) /
      (rule.generation depth).vertices

def ageRootEventNumerator (depth age : ℕ) (p : ℝ) : ℝ :=
  ∑ configuration, FiniteNetwork.bernoulliWeight p configuration *
    ∑ vertex : {vertex : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth vertex = age},
      if event depth vertex.val.val configuration then (1 : ℝ) else 0

def terminalRootEventNumerator (depth : ℕ) (p : ℝ) : ℝ :=
  ∑ configuration, FiniteNetwork.bernoulliWeight p configuration *
    ((if event depth (rule.generation depth).network.source configuration then (1 : ℝ) else 0) +
      (if event depth (rule.generation depth).network.target configuration then (1 : ℝ) else 0))

theorem uniformVertexEventProbability_by_age (depth : ℕ) (p : ℝ) :
    rule.uniformVertexEventProbability event p depth =
      rule.terminalRootEventNumerator event depth p / (rule.generation depth).vertices +
        ∑ age ∈ Finset.range (depth + 1),
          rule.ageRootEventNumerator event depth age p / (rule.generation depth).vertices := by
  unfold uniformVertexEventProbability terminalRootEventNumerator ageRootEventNumerator
  simp_rw [rule.sum_generation_vertices_by_age depth, mul_add]
  rw [Finset.sum_add_distrib, add_div]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def ancestralStageEvent (age n : ℕ) : Set (rule.AncestralSample age) :=
  {sample | event (age + n) (rule.ancestralSampleStageRoot age n sample)
    (rule.ancestralSampleStageConfiguration age n sample)}

theorem measurableSet_ancestralStageEvent (age n : ℕ) :
    MeasurableSet (rule.ancestralStageEvent event age n) := by
  exact ((rule.measurable_ancestralSampleStageRoot age n).prodMk
    (rule.measurable_ancestralSampleStageConfiguration age n))
      ((Set.to_countable {input | event (age + n) input.1 input.2}).measurableSet)

theorem ancestralStageEvent_real_eq
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n : ℕ) (p : unitInterval) :
    (rule.ancestralSampleLaw age p).real (rule.ancestralStageEvent event age n) =
      rule.ageRootEventNumerator event (age + n) age (p : ℝ) /
        Fintype.card (rule.AncestralAgeFiber age n) := by
  have h := rule.ancestralStageJoint_measurePreserving age n p
  have hset : MeasurableSet {input : Fin (rule.generation (age + n)).vertices ×
      FiniteNetwork.Configuration (rule.generation (age + n)).edges |
      event (age + n) input.1 input.2} := (Set.to_countable _).measurableSet
  have heq : (rule.ancestralSampleLaw age p) (rule.ancestralStageEvent event age n) =
      ((rule.ancestralAgeFiberRootLaw age n).prod
        (Measure.pi (fun _ : Fin (rule.generation (age + n)).edges =>
          bernoulliMeasure true false p))) {input | event (age + n) input.1 input.2} := by
    rw [← h.map_eq, Measure.map_apply h.measurable hset]
    rfl
  rw [measureReal_def, heq, ← measureReal_def]
  unfold ancestralAgeFiberRootLaw ageRootEventNumerator
  exact Universality.mappedFiniteUniformBernoulli_event
    (fun vertex : rule.AncestralAgeFiber age n => vertex.val.val) (measurable_of_countable _)
    (rule.generation (age + n)).edges p (event (age + n)) hset

theorem weightedAncestralStageEventProbability
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n : ℕ) (p : unitInterval) :
    rule.finiteRootAgeProbability (age + n) age *
      (rule.ancestralSampleLaw age p).real (rule.ancestralStageEvent event age n) =
      rule.ageRootEventNumerator event (age + n) age (p : ℝ) /
        (rule.generation (age + n)).vertices := by
  rw [rule.ancestralStageEvent_real_eq]
  unfold finiteRootAgeProbability
  have hc : (Fintype.card (rule.AncestralAgeFiber age n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (rule.AncestralAgeFiber age n) ≠ 0)
  have hv : ((rule.generation (age + n)).vertices : ℝ) ≠ 0 := by
    exact_mod_cast (by have := (rule.generation (age + n)).network.two_le_vertices; omega :
      (rule.generation (age + n)).vertices ≠ 0)
  change ((Fintype.card (rule.AncestralAgeFiber age n) : ℝ) /
    (rule.generation (age + n)).vertices) * (_ / Fintype.card (rule.AncestralAgeFiber age n)) = _
  field_simp [hc, hv]

end
end Universality.Rule
