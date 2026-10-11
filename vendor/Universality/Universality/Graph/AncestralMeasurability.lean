import Universality.Graph.FiniteClusterLaw

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- Fixed-age samples use an initial actual vertex, an ancestral edge sequence,
and independent raw coordinates. The sample type does not involve a random
quotient type; the actual direct-limit graph is constructed from each sample. -/
abbrev AncestralSample (rule : Rule) (age : ℕ) :=
  Fin (rule.generation age).vertices × ((ℕ → Fin rule.edges) ×
    ((Σ n, Fin (rule.generation (age + n)).edges) → Bool))

def ancestralSampleStageConfiguration (rule : Rule) (age n : ℕ)
    (sample : rule.AncestralSample age) : FiniteNetwork.Configuration (rule.generation (age + n)).edges :=
  (rule.ancestralTower age sample.2.1).stageConfiguration (fun k e => sample.2.2 ⟨k, e⟩) n

def ancestralSampleStageRoot (rule : Rule) (age n : ℕ)
    (sample : rule.AncestralSample age) : Fin (rule.generation (age + n)).vertices :=
  (rule.ancestralTower age sample.2.1).vertexMap 0 n (Nat.zero_le n) sample.1

theorem measurable_ancestralSampleStageConfiguration (rule : Rule) (age n : ℕ) :
    Measurable (rule.ancestralSampleStageConfiguration age n) := by
  have hraw (k : ℕ) : Measurable (fun sample : rule.AncestralSample age =>
      fun e : Fin (rule.generation (age + k)).edges => sample.2.2 ⟨k, e⟩) :=
    measurable_pi_lambda _ (fun e => (measurable_pi_apply
      (⟨k, e⟩ : Σ j, Fin (rule.generation (age + j)).edges)).comp
      (measurable_snd.comp measurable_snd))
  induction n with
  | zero => exact hraw 0
  | succ n ih =>
    let step (edge : Fin rule.edges) :
        (rule.generation (age + n)).network.NetworkEmbedding
          (rule.generation (age + (n + 1))).network :=
      (Nat.add_assoc age n 1) ▸ rule.generationCellEmbedding (age + n) edge
    have hfinite : Measurable (fun input : Fin rule.edges ×
        (FiniteNetwork.Configuration (rule.generation (age + n)).edges ×
          FiniteNetwork.Configuration (rule.generation (age + (n + 1))).edges) =>
      Function.extend (step input.1).edge input.2.1 input.2.2) := measurable_of_countable _
    have heq : rule.ancestralSampleStageConfiguration age (n + 1) =
        (fun sample : rule.AncestralSample age =>
          Function.extend (step (sample.2.1 n)).edge
            (rule.ancestralSampleStageConfiguration age n sample)
            (fun e => sample.2.2 ⟨n + 1, e⟩)) := by
      rfl
    rw [heq]
    have haddress : Measurable (fun sample : rule.AncestralSample age => sample.2.1 n) :=
      (measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)
    have hinput : Measurable (fun sample : rule.AncestralSample age =>
        (sample.2.1 n, (rule.ancestralSampleStageConfiguration age n sample,
          fun e : Fin (rule.generation (age + (n + 1))).edges => sample.2.2 ⟨n + 1, e⟩))) :=
      haddress.prodMk (ih.prodMk (hraw (n + 1)))
    intro target htarget
    exact hinput (hfinite htarget)

theorem measurable_ancestralSampleStageRoot (rule : Rule) (age n : ℕ) :
    Measurable (rule.ancestralSampleStageRoot age n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    let step (edge : Fin rule.edges) :
        (rule.generation (age + n)).network.NetworkEmbedding
          (rule.generation (age + (n + 1))).network :=
      (Nat.add_assoc age n 1) ▸ rule.generationCellEmbedding (age + n) edge
    have heq : rule.ancestralSampleStageRoot age (n + 1) =
        (fun sample => (step (sample.2.1 n)).vertex
          (rule.ancestralSampleStageRoot age n sample)) := by
      funext sample
      simp only [ancestralSampleStageRoot, NetworkTower.vertexMap,
        Nat.leRecOn_succ (Nat.zero_le n)]
      rfl
    rw [heq]
    have hfinite : Measurable (fun input : Fin rule.edges ×
        Fin (rule.generation (age + n)).vertices => (step input.1).vertex input.2) :=
      measurable_of_countable _
    have haddress : Measurable (fun sample : rule.AncestralSample age => sample.2.1 n) :=
      (measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)
    have hinput : Measurable (fun sample : rule.AncestralSample age =>
        (sample.2.1 n, rule.ancestralSampleStageRoot age n sample)) := haddress.prodMk ih
    intro target htarget
    exact hinput (hfinite htarget)

def ancestralSampleStageClusterSize (rule : Rule) (age n : ℕ)
    (sample : rule.AncestralSample age) : ℕ :=
  ((rule.generation (age + n)).network.clusterVertices
    (rule.ancestralSampleStageConfiguration age n sample)
    (rule.ancestralSampleStageRoot age n sample)).card

theorem measurable_ancestralSampleStageClusterSize (rule : Rule) (age n : ℕ) :
    Measurable (rule.ancestralSampleStageClusterSize age n) := by
  unfold ancestralSampleStageClusterSize
  have hfinite : Measurable (fun input :
      FiniteNetwork.Configuration (rule.generation (age + n)).edges ×
        Fin (rule.generation (age + n)).vertices =>
    ((rule.generation (age + n)).network.clusterVertices input.1 input.2).card) :=
    measurable_of_countable _
  have hinput : Measurable (fun sample : rule.AncestralSample age =>
      (rule.ancestralSampleStageConfiguration age n sample,
        rule.ancestralSampleStageRoot age n sample)) :=
    (rule.measurable_ancestralSampleStageConfiguration age n).prodMk
      (rule.measurable_ancestralSampleStageRoot age n)
  intro target htarget
  exact hinput (hfinite htarget)

/-- The event is defined using the actual graph associated with each spine,
but is measurable on the ordinary fixed product sample space. -/
def ancestralSampleFiniteClusterSizeEvent (rule : Rule) (age size : ℕ)
    (sample : rule.AncestralSample age) : Prop :=
  (rule.ancestralTower age sample.2.1).finiteClusterSizeEvent
    ((rule.ancestralTower age sample.2.1).sampledConfiguration sample.2.2) sample.1 size

theorem measurableSet_ancestralSampleFiniteClusterSizeEvent (rule : Rule) (age size : ℕ) :
    MeasurableSet {sample | rule.ancestralSampleFiniteClusterSizeEvent age size sample} := by
  simp only [ancestralSampleFiniteClusterSizeEvent,
    NetworkTower.finiteClusterSizeEvent_iff_eventually_card, Set.setOf_exists, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro first
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro h
  exact (rule.measurable_ancestralSampleStageClusterSize age n) (measurableSet_singleton size)

theorem ancestralSampleFiniteClusterSize_probability_tendsto (rule : Rule) (age size : ℕ)
    (law : Measure (rule.AncestralSample age)) [IsProbabilityMeasure law] :
    Tendsto (fun n => law.real {sample | rule.ancestralSampleStageClusterSize age n sample = size})
      atTop (𝓝 (law.real {sample | rule.ancestralSampleFiniteClusterSizeEvent age size sample})) := by
  classical
  have hstage (n : ℕ) : MeasurableSet
      {sample | rule.ancestralSampleStageClusterSize age n sample = size} :=
    (rule.measurable_ancestralSampleStageClusterSize age n) (measurableSet_singleton size)
  have hlimit := rule.measurableSet_ancestralSampleFiniteClusterSizeEvent age size
  have hintegral := tendsto_integral_of_dominated_convergence (μ := law)
    (fun _ => (1 : ℝ))
    (F := fun n => {sample | rule.ancestralSampleStageClusterSize age n sample = size}.indicator
      (fun _ => (1 : ℝ)))
    (f := {sample | rule.ancestralSampleFiniteClusterSizeEvent age size sample}.indicator
      (fun _ => (1 : ℝ)))
    (fun n => (measurable_const.indicator (hstage n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun sample => by
      simp only [Set.indicator_apply]
      split <;> norm_num))
    (Eventually.of_forall (fun sample => by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, ancestralSampleStageClusterSize,
        ancestralSampleStageConfiguration, ancestralSampleStageRoot,
        ancestralSampleFiniteClusterSizeEvent, NetworkTower.sampledConfiguration,
        NetworkTower.restrict_configuration, ancestralTower] using
        (rule.ancestralTower age sample.2.1).finite_cluster_size_indicator_tendsto
          ((rule.ancestralTower age sample.2.1).sampledConfiguration sample.2.2) sample.1 size))
  simpa only [integral_indicator_const (1 : ℝ) (hstage _),
    integral_indicator_const (1 : ℝ) hlimit, smul_eq_mul, mul_one] using hintegral

end
end Universality.Rule
