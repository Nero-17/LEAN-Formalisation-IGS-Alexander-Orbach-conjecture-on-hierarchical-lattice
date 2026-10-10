import Universality.Graph.AncestralInterior
import Universality.Graph.AncestralMeasurability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Bernoulli

namespace Universality.FiniteNetwork
variable {vertices edges : ℕ}

instance interiorVertexMeasurableSpace (network : FiniteNetwork vertices edges) :
    MeasurableSpace network.InteriorVertex := ⊤

instance interiorVertexMeasurableSingletonClass (network : FiniteNetwork vertices edges) :
    MeasurableSingletonClass network.InteriorVertex := ⟨fun _ => trivial⟩

end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def ancestralInitialRootLaw (rule : Rule) [Nonempty rule.network.InteriorVertex] (age : ℕ) :
    Measure (Fin (rule.generation age).vertices) :=
  (PMF.uniformOfFintype rule.network.InteriorVertex).toMeasure.map
    (fun seed => (rule.ancestralRootInterior age seed).val)

instance ancestralInitialRootLaw_probability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] (age : ℕ) :
    IsProbabilityMeasure (rule.ancestralInitialRootLaw age) := by
  unfold ancestralInitialRootLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

def ancestralSpineLaw (rule : Rule) [NeZero rule.edges] : Measure (ℕ → Fin rule.edges) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin rule.edges)).toMeasure)

instance ancestralSpineLaw_probability (rule : Rule) [NeZero rule.edges] :
    IsProbabilityMeasure rule.ancestralSpineLaw := by
  unfold ancestralSpineLaw
  infer_instance

def ancestralRawEdgeLaw (rule : Rule) (age : ℕ) (p : unitInterval) :
    Measure ((Σ n, Fin (rule.generation (age + n)).edges) → Bool) :=
  Measure.infinitePi (fun _ : Σ n, Fin (rule.generation (age + n)).edges =>
    bernoulliMeasure true false p)

instance ancestralRawEdgeLaw_probability (rule : Rule) (age : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (rule.ancestralRawEdgeLaw age p) := by
  unfold ancestralRawEdgeLaw
  infer_instance

/-- A concrete independently sampled rooted graph: choose a uniform original
interior root, independent uniform ancestral edges, and independent Bernoulli
edge coordinates. No limiting cluster distribution is used in this definition. -/
def ancestralSampleLaw (rule : Rule) [Nonempty rule.network.InteriorVertex]
    [NeZero rule.edges] (age : ℕ) (p : unitInterval) : Measure (rule.AncestralSample age) :=
  (rule.ancestralInitialRootLaw age).prod
    (rule.ancestralSpineLaw.prod (rule.ancestralRawEdgeLaw age p))

instance ancestralSampleLaw_probability (rule : Rule) [Nonempty rule.network.InteriorVertex]
    [NeZero rule.edges] (age : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (rule.ancestralSampleLaw age p) := by
  unfold ancestralSampleLaw
  infer_instance

theorem ancestralStageConfiguration_measurePreserving (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges) (p : unitInterval) (n : ℕ) :
    MeasurePreserving (fun bits => (rule.ancestralTower age address).stageConfiguration
        (fun k e => bits ⟨k, e⟩) n)
      (rule.ancestralRawEdgeLaw age p)
      (Measure.pi (fun _ : Fin (rule.generation (age + n)).edges => bernoulliMeasure true false p)) :=
  (rule.ancestralTower age address).stageConfiguration_measurePreserving
    (bernoulliMeasure true false p) n

def ancestralFiniteClusterProbability (rule : Rule) [Nonempty rule.network.InteriorVertex]
    [NeZero rule.edges] (age size : ℕ) (p : unitInterval) : ℝ :=
  (rule.ancestralSampleLaw age p).real
    {sample | rule.ancestralSampleFiniteClusterSizeEvent age size sample}

theorem ancestralFiniteClusterProbability_tendsto (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age size : ℕ) (p : unitInterval) :
    Tendsto (fun n => (rule.ancestralSampleLaw age p).real
      {sample | rule.ancestralSampleStageClusterSize age n sample = size}) atTop
        (𝓝 (rule.ancestralFiniteClusterProbability age size p)) :=
  rule.ancestralSampleFiniteClusterSize_probability_tendsto age size (rule.ancestralSampleLaw age p)

end
end Universality.Rule
