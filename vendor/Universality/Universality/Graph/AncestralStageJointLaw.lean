import Universality.Graph.AncestralStageRootLaw

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- The physical finite-stage root and all finite-stage edge bits are
independent, with the uniform actual age-fibre law and Bernoulli product law.
The configuration depends on the same ancestral spine as the root; the proof
uses its already established constant conditional product law. -/
theorem ancestralStageJoint_measurePreserving (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n : ℕ) (p : unitInterval) :
    MeasurePreserving (fun sample : rule.AncestralSample age =>
      (rule.ancestralSampleStageRoot age n sample,
        rule.ancestralSampleStageConfiguration age n sample))
      (rule.ancestralSampleLaw age p)
      ((rule.ancestralAgeFiberRootLaw age n).prod
        (Measure.pi (fun _ : Fin (rule.generation (age + n)).edges =>
          bernoulliMeasure true false p))) := by
  let configuration : (Fin (rule.generation age).vertices × (ℕ → Fin rule.edges)) →
      ((Σ k, Fin (rule.generation (age + k)).edges) → Bool) →
        FiniteNetwork.Configuration (rule.generation (age + n)).edges :=
    fun input bits => (rule.ancestralTower age input.2).stageConfiguration
      (fun k e => bits ⟨k, e⟩) n
  have hconfiguration : Measurable (Function.uncurry configuration) := by
    intro target htarget
    exact MeasurableEquiv.prodAssoc.measurable
      ((rule.measurable_ancestralSampleStageConfiguration age n) htarget)
  have hconditional : ∀ᵐ input ∂(rule.ancestralInitialRootLaw age).prod rule.ancestralSpineLaw,
      Measure.map (configuration input) (rule.ancestralRawEdgeLaw age p) =
        Measure.pi (fun _ : Fin (rule.generation (age + n)).edges =>
          bernoulliMeasure true false p) :=
    Filter.Eventually.of_forall (fun input =>
      (rule.ancestralStageConfiguration_measurePreserving age input.2 p n).map_eq)
  have hskew := (rule.ancestralRootAtStage_measurePreserving age n).skew_product
    hconfiguration hconditional
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (rule.ancestralInitialRootLaw age)
      rule.ancestralSpineLaw (rule.ancestralRawEdgeLaw age p))
  exact hskew.comp hassoc

/-- An exact event-level version of the joint law, before passing to any
infinite-volume limit. -/
theorem ancestralStageClusterSize_probability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n size : ℕ) (p : unitInterval) :
    (rule.ancestralSampleLaw age p)
        {sample | rule.ancestralSampleStageClusterSize age n sample = size} =
      ((rule.ancestralAgeFiberRootLaw age n).prod
        (Measure.pi (fun _ : Fin (rule.generation (age + n)).edges =>
          bernoulliMeasure true false p)))
        {input | ((rule.generation (age + n)).network.clusterVertices input.2 input.1).card = size} := by
  have h := rule.ancestralStageJoint_measurePreserving age n p
  have hset : MeasurableSet
      {input : Fin (rule.generation (age + n)).vertices ×
        FiniteNetwork.Configuration (rule.generation (age + n)).edges |
        ((rule.generation (age + n)).network.clusterVertices input.2 input.1).card = size} :=
    Set.to_countable _ |>.measurableSet
  rw [← h.map_eq, Measure.map_apply h.measurable hset]
  rfl

end
end Universality.Rule
