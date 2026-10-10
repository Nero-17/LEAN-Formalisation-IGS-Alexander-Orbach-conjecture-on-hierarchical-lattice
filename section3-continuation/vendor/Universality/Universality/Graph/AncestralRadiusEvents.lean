import Universality.Graph.TowerRadiusEvents
import Universality.Graph.AncestralTowerIsometry
import Universality.Graph.UniformRootProbabilitySpace

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def ancestralSampleStageRadius (rule : Rule) (age n : ℕ) (sample : rule.AncestralSample age) : ℕ :=
  (rule.generation (age + n)).network.rootClusterRadius
    (rule.ancestralSampleStageConfiguration age n sample) (rule.ancestralSampleStageRoot age n sample)

def uniformRootRadiusTailEvent (rule : Rule) (radius : ℕ) (sample : rule.UniformRootSample) : Prop :=
  (rule.ancestralTower sample.1 sample.2.2.1).radiusTailEvent
    ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2) sample.2.1 radius

theorem ancestral_stageRootClusterRadius (rule : Rule) (age n : ℕ) (sample : rule.AncestralSample age) :
    (rule.ancestralTower age sample.2.1).stageRootClusterRadius
      ((rule.ancestralTower age sample.2.1).sampledConfiguration sample.2.2) sample.1 n =
        rule.ancestralSampleStageRadius age n sample := by
  unfold NetworkTower.stageRootClusterRadius NetworkTower.sampledConfiguration
  rw [NetworkTower.restrict_configuration]
  rfl

theorem measurable_ancestralSampleStageRadius (rule : Rule) (age n : ℕ) :
    Measurable (rule.ancestralSampleStageRadius age n) := by
  have hinput : Measurable (fun sample : rule.AncestralSample age =>
      (rule.ancestralSampleStageRoot age n sample,
        rule.ancestralSampleStageConfiguration age n sample)) :=
    (rule.measurable_ancestralSampleStageRoot age n).prodMk
      (rule.measurable_ancestralSampleStageConfiguration age n)
  have hresponse : Measurable (fun input : Fin (rule.generation (age + n)).vertices ×
      FiniteNetwork.Configuration (rule.generation (age + n)).edges =>
      (rule.generation (age + n)).network.rootClusterRadius input.2 input.1) := measurable_of_countable _
  intro event hevent
  exact hinput (hresponse hevent)

theorem Classical.uniformRootRadiusTailEvent_iff_exists_stage {rule : Rule} (h : rule.Classical)
    (radius : ℕ) (sample : rule.UniformRootSample) :
    rule.uniformRootRadiusTailEvent radius sample ↔
      ∃ n, radius ≤ rule.ancestralSampleStageRadius sample.1 n sample.2 := by
  have hresult := (rule.ancestralTower sample.1 sample.2.2.1).radiusTailEvent_iff_exists_stage
    (h.ancestralTower_isometricSteps sample.1 sample.2.2.1)
    (fun n => (h.generation (sample.1 + n)).connected)
    ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2)
    sample.2.1 radius
  simpa only [rule.ancestral_stageRootClusterRadius, uniformRootRadiusTailEvent] using hresult

theorem Classical.measurableSet_uniformRootRadiusTailEvent {rule : Rule} (h : rule.Classical)
    (radius : ℕ) : MeasurableSet {sample | rule.uniformRootRadiusTailEvent radius sample} := by
  apply (Universality.measurableSet_ageSample_iff _).mpr
  intro age
  change MeasurableSet {sample : rule.AncestralSample age |
    rule.uniformRootRadiusTailEvent radius ⟨age, sample⟩}
  simp only [h.uniformRootRadiusTailEvent_iff_exists_stage, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro n
  exact rule.measurable_ancestralSampleStageRadius age n (Set.to_countable _).measurableSet

theorem Classical.ancestral_radiusTailEvent_stabilizes {rule : Rule} (h : rule.Classical)
    (age radius : ℕ) (sample : rule.AncestralSample age) :
    ∀ᶠ n in atTop, (radius ≤ rule.ancestralSampleStageRadius age n sample) ↔
      rule.uniformRootRadiusTailEvent radius ⟨age, sample⟩ := by
  have hresult := (rule.ancestralTower age sample.2.1).radiusTailEvent_stage_stabilizes
    (h.ancestralTower_isometricSteps age sample.2.1)
    (fun n => (h.generation (age + n)).connected)
    ((rule.ancestralTower age sample.2.1).sampledConfiguration sample.2.2) sample.1 radius
  simpa only [rule.ancestral_stageRootClusterRadius, uniformRootRadiusTailEvent] using hresult

end
end Universality.Rule
