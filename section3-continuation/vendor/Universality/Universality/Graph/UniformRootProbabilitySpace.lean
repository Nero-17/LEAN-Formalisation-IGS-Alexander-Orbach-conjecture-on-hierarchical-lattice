import Universality.Graph.AncestralProbabilitySpace
import Universality.Graph.CountableAgeMixture
import Universality.Graph.RootAgeLaw

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

abbrev UniformRootSample (rule : Rule) := Σ age, rule.AncestralSample age

/-- The actual graph law with the age distribution derived from finite uniform
vertices, followed by uniform ancestry and independent Bernoulli edge bits. -/
def uniformRootSampleLaw (rule : Rule) [Nonempty rule.network.InteriorVertex]
    [NeZero rule.edges] (hedges : 1 < rule.edges) (p : unitInterval) :
    Measure rule.UniformRootSample :=
  Universality.countableAgeMixture (rule.rootAgeLaw hedges)
    (fun age => rule.ancestralSampleLaw age p)

instance uniformRootSampleLaw_probability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) :
    IsProbabilityMeasure (rule.uniformRootSampleLaw hedges p) := by
  unfold uniformRootSampleLaw
  infer_instance

def uniformRootFiniteClusterSizeEvent (rule : Rule) (size : ℕ)
    (sample : rule.UniformRootSample) : Prop :=
  rule.ancestralSampleFiniteClusterSizeEvent sample.1 size sample.2

theorem measurableSet_uniformRootFiniteClusterSizeEvent (rule : Rule) (size : ℕ) :
    MeasurableSet {sample | rule.uniformRootFiniteClusterSizeEvent size sample} := by
  apply (Universality.measurableSet_ageSample_iff _).mpr
  intro age
  exact rule.measurableSet_ancestralSampleFiniteClusterSizeEvent age size

def uniformRootFiniteClusterProbability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) (size : ℕ) : ℝ :=
  (rule.uniformRootSampleLaw hedges p).real
    {sample | rule.uniformRootFiniteClusterSizeEvent size sample}

theorem uniformRootFiniteClusterProbability_eq_mixture (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) (size : ℕ) :
    rule.uniformRootFiniteClusterProbability hedges p size =
      ∑' age, (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1)) *
        rule.ancestralFiniteClusterProbability age size p := by
  unfold uniformRootFiniteClusterProbability uniformRootSampleLaw
  rw [Universality.countableAgeMixture_real_apply _ _
    (rule.measurableSet_uniformRootFiniteClusterSizeEvent size)]
  apply tsum_congr
  intro age
  rw [rule.rootAgeLaw_real_singleton]
  rfl

def uniformRootInfiniteClusterEvent (rule : Rule) (sample : rule.UniformRootSample) : Prop :=
  ¬ ∃ size, rule.uniformRootFiniteClusterSizeEvent size sample

/-- The residual event is exactly an infinite connected component in the
sampled direct-limit graph, including without any local-finiteness assumption. -/
theorem uniformRootInfiniteClusterEvent_iff (rule : Rule) (sample : rule.UniformRootSample) :
    rule.uniformRootInfiniteClusterEvent sample ↔
      Set.Infinite {vertex |
        ((rule.ancestralTower sample.1 sample.2.2.1).openGraph
          ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2)).Reachable
            ((rule.ancestralTower sample.1 sample.2.2.1).vertex 0 sample.2.1) vertex} :=
  (rule.ancestralTower sample.1 sample.2.2.1).no_finiteClusterSizeEvent_iff_infinite
    ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2) sample.2.1

theorem measurableSet_uniformRootInfiniteClusterEvent (rule : Rule) :
    MeasurableSet {sample | rule.uniformRootInfiniteClusterEvent sample} := by
  change MeasurableSet {sample | ∃ size, rule.uniformRootFiniteClusterSizeEvent size sample}ᶜ
  rw [Set.setOf_exists]
  exact (MeasurableSet.iUnion (fun size =>
    rule.measurableSet_uniformRootFiniteClusterSizeEvent size)).compl

theorem uniformRootInfiniteClusterProbability_eq (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) :
    (rule.uniformRootSampleLaw hedges p).real
        {sample | rule.uniformRootInfiniteClusterEvent sample} =
      1 - ∑' size, rule.uniformRootFiniteClusterProbability hedges p size := by
  have hdisjoint : Pairwise (fun first second =>
      Disjoint {sample | rule.uniformRootFiniteClusterSizeEvent first sample}
        {sample | rule.uniformRootFiniteClusterSizeEvent second sample}) := by
    intro first second hne
    apply Set.disjoint_left.mpr
    intro sample hfirst hsecond
    exact hne ((rule.ancestralTower sample.1 sample.2.2.1).finiteClusterSizeEvent_unique
      ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2)
      sample.2.1 hfirst hsecond)
  have hmeasurable := fun size => rule.measurableSet_uniformRootFiniteClusterSizeEvent size
  change (rule.uniformRootSampleLaw hedges p).real
    {sample | ∃ size, rule.uniformRootFiniteClusterSizeEvent size sample}ᶜ = _
  rw [Set.setOf_exists]
  rw [probReal_compl_eq_one_sub (MeasurableSet.iUnion hmeasurable)]
  congr 1
  rw [measureReal_def, measure_iUnion hdisjoint hmeasurable,
    ENNReal.tsum_toReal_eq (fun size => measure_ne_top (rule.uniformRootSampleLaw hedges p) _)]
  rfl

end
end Universality.Rule
