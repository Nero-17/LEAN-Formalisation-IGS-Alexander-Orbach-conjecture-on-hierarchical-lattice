import Universality.Graph.AncestralLocalFiniteness
import Universality.Graph.UniformRootProbabilitySpace
import Universality.Percolation.ClassicalClusterNumber

namespace Universality
noncomputable section
open MeasureTheory

theorem ae_countableAgeMixture {sample : ℕ → Type*}
    [∀ age, MeasurableSpace (sample age)] (ageLaw : Measure ℕ)
    (law : ∀ age, Measure (sample age)) (predicate : (Σ age, sample age) → Prop)
    (hmeasurable : MeasurableSet {sample | predicate sample})
    (heventual : ∀ age, ∀ᵐ sample ∂law age, predicate ⟨age, sample⟩) :
    ∀ᵐ sample ∂countableAgeMixture ageLaw law, predicate sample := by
  unfold countableAgeMixture
  apply Measure.ae_sum_iff.mpr
  intro age
  apply Measure.ae_smul_measure
  exact (ae_map_iff (measurable_ageSampleEmbedding age).aemeasurable hmeasurable).mpr
    (heventual age)

end
end Universality

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter

def ancestralAllTailRootsInternal (rule : Rule) (age : ℕ) (address : ℕ → Fin rule.edges) : Prop :=
  ∀ (start : ℕ) (vertex : Fin (rule.generation (age + start)).vertices), ∃ n,
    rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
        (rule.generation ((age + start) + n)).network.source ∧
    rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
        (rule.generation ((age + start) + n)).network.target

theorem measurableSet_ancestralAllTailRootsInternal (rule : Rule) (age : ℕ) :
    MeasurableSet {address | rule.ancestralAllTailRootsInternal age address} := by
  simp only [ancestralAllTailRootsInternal, Set.setOf_forall, Set.setOf_exists]
  apply MeasurableSet.iInter
  intro start
  apply MeasurableSet.iInter
  intro vertex
  apply MeasurableSet.iUnion
  intro n
  have hinput : Measurable (fun address : ℕ → Fin rule.edges =>
      (vertex, fun k => address (start + k))) :=
    measurable_const.prodMk (measurable_pi_lambda _ (fun k => measurable_pi_apply (start + k)))
  have hroot : Measurable (fun address : ℕ → Fin rule.edges =>
      rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k))) := by
    intro event hevent
    exact hinput ((rule.measurable_ancestralRootAtStage (age + start) n) hevent)
  exact (hroot (measurableSet_singleton _).compl).inter
    (hroot (measurableSet_singleton _).compl)

theorem ancestralAllTailRootsInternal_eventuallyInternal (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges) (hgood : rule.ancestralAllTailRootsInternal age address) :
    (rule.ancestralTower age address).EventuallyInternal := by
  apply (rule.ancestralTower age address).eventuallyInternal_of_tails
  intro start
  exact (rule.ancestralTail_eventually_internal_iff age start address).mpr (hgood start)

theorem Classical.ae_ancestralAllTailRootsInternal {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age : ℕ) :
    ∀ᵐ address ∂rule.ancestralSpineLaw, rule.ancestralAllTailRootsInternal age address := by
  apply ae_all_iff.mpr
  intro start
  have hall := ae_all_iff.mpr (fun vertex =>
    h.ae_ancestral_stage_eventually_internal (age + start) vertex)
  exact (rule.ancestralSpine_shift_measurePreserving start).quasiMeasurePreserving.ae hall

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def uniformRootAllTailRootsInternal (rule : Rule) (sample : rule.UniformRootSample) : Prop :=
  rule.ancestralAllTailRootsInternal sample.1 sample.2.2.1

omit [MeasurableSingletonClass Bool] in
theorem measurableSet_uniformRootAllTailRootsInternal (rule : Rule) :
    MeasurableSet {sample | rule.uniformRootAllTailRootsInternal sample} := by
  apply (Universality.measurableSet_ageSample_iff _).mpr
  intro age
  exact measurable_snd.fst (rule.measurableSet_ancestralAllTailRootsInternal age)

omit [MeasurableSingletonClass Bool] in
theorem Classical.ae_uniformRootAllTailRootsInternal {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) :
    ∀ᵐ sample ∂rule.uniformRootSampleLaw h.edges_gt_one p,
      rule.uniformRootAllTailRootsInternal sample := by
  apply Universality.ae_countableAgeMixture _ _ _
    rule.measurableSet_uniformRootAllTailRootsInternal
  intro age
  have hspine : MeasurePreserving (fun sample : rule.AncestralSample age => sample.2.1)
      (rule.ancestralSampleLaw age p) rule.ancestralSpineLaw :=
    (measurePreserving_fst (μ := rule.ancestralSpineLaw) (ν := rule.ancestralRawEdgeLaw age p)).comp
      (measurePreserving_snd (μ := rule.ancestralInitialRootLaw age)
        (ν := rule.ancestralSpineLaw.prod (rule.ancestralRawEdgeLaw age p)))
  exact hspine.quasiMeasurePreserving.ae (h.ae_ancestralAllTailRootsInternal age)

omit [MeasurableSingletonClass Bool] in
/-- Local finiteness for the complete physical uniform-root law, including
the actual root-age mixture and all Bernoulli parameters. -/
theorem Classical.ae_uniformRoot_finite_neighborSet {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) :
    ∀ᵐ sample ∂rule.uniformRootSampleLaw h.edges_gt_one p,
      ∀ (configuration : (rule.ancestralTower sample.1 sample.2.2.1).Edge → Bool)
        (vertex : (rule.ancestralTower sample.1 sample.2.2.1).Vertex),
        (((rule.ancestralTower sample.1 sample.2.2.1).openGraph configuration).neighborSet vertex).Finite := by
  filter_upwards [h.ae_uniformRootAllTailRootsInternal p] with sample hsample
  exact rule.ancestralTower_finite_neighborSet_of_eventuallyInternal sample.1 sample.2.2.1
    (rule.ancestralAllTailRootsInternal_eventuallyInternal sample.1 sample.2.2.1 hsample)

end
end Universality.Rule
