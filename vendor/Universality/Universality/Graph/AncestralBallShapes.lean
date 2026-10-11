import Universality.Graph.TowerRootedBallIsomorphism
import Universality.Graph.UniformRootLocalFiniteness
import Universality.Graph.AncestralTowerIsometry
namespace Universality.FiniteNetwork
noncomputable section

def ambientBallRoot {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (root : Fin vertices) (radius : ℕ) : {vertex // network.fullGraph.dist root vertex ≤ radius} :=
  ⟨root, by simp⟩

def ambientBallShape {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (root : Fin vertices) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) : Prop :=
  RootedGraphIsomorphic
    ((network.openGraph configuration).induce {vertex | network.fullGraph.dist root vertex ≤ radius})
    (network.ambientBallRoot root radius) targetGraph targetRoot

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def generationFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target)
    (depth : ℕ) (root : Fin (rule.generation depth).vertices)
    (_configuration : FiniteNetwork.Configuration (rule.generation depth).edges) : Prop :=
  (rule.generation depth).network.ambientBallShape (fun _ => true) root radius targetGraph targetRoot

def ancestralStageFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target)
    (age n : ℕ) : Set (rule.AncestralSample age) :=
  {sample | rule.generationFullBallShape radius targetGraph targetRoot (age + n)
    (rule.ancestralSampleStageRoot age n sample)
    (rule.ancestralSampleStageConfiguration age n sample)}

def uniformRootFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target)
    (sample : rule.UniformRootSample) : Prop :=
  RootedGraphIsomorphic
    (((rule.ancestralTower sample.1 sample.2.2.1).openGraph
      (fun _ => true)).induce
        ((rule.ancestralTower sample.1 sample.2.2.1).ambientBall sample.2.1 radius))
    ((rule.ancestralTower sample.1 sample.2.2.1).ambientBallRoot sample.2.1 radius)
    targetGraph targetRoot

theorem measurableSet_ancestralStageFullBallShape (rule : Rule) (radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) (age n : ℕ) :
    MeasurableSet (rule.ancestralStageFullBallShape radius targetGraph targetRoot age n) := by
  have hinput : Measurable (fun sample : rule.AncestralSample age =>
      (rule.ancestralSampleStageRoot age n sample,
        rule.ancestralSampleStageConfiguration age n sample)) :=
    (rule.measurable_ancestralSampleStageRoot age n).prodMk
      (rule.measurable_ancestralSampleStageConfiguration age n)
  exact hinput (Set.to_countable {input : Fin (rule.generation (age + n)).vertices ×
    FiniteNetwork.Configuration (rule.generation (age + n)).edges |
      rule.generationFullBallShape radius targetGraph targetRoot (age + n) input.1 input.2}).measurableSet

omit [MeasurableSingletonClass Bool] in
theorem ancestralSampleSpine_measurePreserving (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age : ℕ) (p : unitInterval) :
    MeasurePreserving (fun sample : rule.AncestralSample age => sample.2.1)
      (rule.ancestralSampleLaw age p) rule.ancestralSpineLaw :=
  (measurePreserving_fst (μ := rule.ancestralSpineLaw) (ν := rule.ancestralRawEdgeLaw age p)).comp
    (measurePreserving_snd (μ := rule.ancestralInitialRootLaw age)
      (ν := rule.ancestralSpineLaw.prod (rule.ancestralRawEdgeLaw age p)))

omit [MeasurableSpace Bool] [MeasurableSingletonClass Bool] in
theorem Classical.ancestral_fullBallShape_stabilizes_of_finite_neighbors {rule : Rule}
    (h : rule.Classical) (age radius : ℕ) (sample : rule.AncestralSample age)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target)
    (hfinite : ∀ vertex,
      (((rule.ancestralTower age sample.2.1).openGraph (fun _ => true)).neighborSet vertex).Finite) :
    ∀ᶠ n in atTop,
      sample ∈ rule.ancestralStageFullBallShape radius targetGraph targetRoot age n ↔
        rule.uniformRootFullBallShape radius targetGraph targetRoot ⟨age, sample⟩ := by
  have hisomorphisms := (rule.ancestralTower age sample.2.1).eventually_rootedBall_isomorphism
    (h.ancestralTower_isometricSteps age sample.2.1)
    (fun n => (h.generation (age + n)).connected)
    hfinite
    (fun _ => true)
    sample.1 radius
  filter_upwards [hisomorphisms] with n hn
  obtain ⟨isomorphism, hroot⟩ := hn
  exact rootedGraphIsomorphic_iff targetGraph targetRoot isomorphism hroot

omit [MeasurableSingletonClass Bool] in
theorem Classical.ae_ancestral_fullBallShape_stabilizes {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (age radius : ℕ)
    {Target : Type*} (targetGraph : SimpleGraph Target) (targetRoot : Target) :
    ∀ᵐ sample ∂rule.ancestralSampleLaw age p, ∀ᶠ n in atTop,
      sample ∈ rule.ancestralStageFullBallShape radius targetGraph targetRoot age n ↔
        rule.uniformRootFullBallShape radius targetGraph targetRoot ⟨age, sample⟩ := by
  have hfinite := (rule.ancestralSampleSpine_measurePreserving age p).quasiMeasurePreserving.ae
    (h.ae_ancestralTower_finite_neighborSet age)
  filter_upwards [hfinite] with sample hsample
  exact h.ancestral_fullBallShape_stabilizes_of_finite_neighbors age radius sample
    targetGraph targetRoot (hsample (fun _ => true))

end
end Universality.Rule
