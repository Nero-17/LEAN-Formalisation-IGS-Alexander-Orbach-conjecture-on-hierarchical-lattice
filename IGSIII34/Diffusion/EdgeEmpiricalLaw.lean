import IGSIII34.Diffusion.EdgeFinitePartition
import IGSIII34.Diffusion.ActualFiniteWalk
import IGSIII.Geometry.FullComponentMassApproximation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem markedComponentEdgeMass_root_positive (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) : 0 < markedComponentEdgeMass rule marks depth [] := by
  have rootCrossing := markedGenerationConfiguration_crosses rule marks crossing depth [] true
  letI := clusterEdge_nonempty (rule.generation depth).network _ rootCrossing
  simp only [markedComponentEdgeMass, markedOrientedEdgeMass, componentEdgeAddress, List.map_nil,
    retainedComponentState, retainedComponentStateFrom, OrientedState.massOpened, decide_true]
  rw [orientedEdgeReward_connected _ _ rootCrossing, ← clusterEdge_card]
  exact_mod_cast Fintype.card_pos

def edgeComponentWordWeight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) : ℝ :=
  markedComponentEdgeMass rule marks fine (List.ofFn word) /
    markedComponentEdgeMass rule marks (fine + age) []

theorem edgeComponentWordWeight_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) :
    0 ≤ edgeComponentWordWeight rule marks fine age word := by
  unfold edgeComponentWordWeight markedComponentEdgeMass markedOrientedEdgeMass orientedEdgeReward orientedLiveCount
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro edge _ <;> split_ifs <;> norm_num

theorem edgeComponentWordWeight_sum (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : ∑ word, edgeComponentWordWeight rule marks fine age word = 1 := by
  unfold edgeComponentWordWeight
  rw [← Finset.sum_div]
  have partition := actual_component_edge_finite_partition rule marks crossing fine age []
  simp only [List.nil_append] at partition
  rw [← partition, div_self (markedComponentEdgeMass_root_positive rule marks crossing _).ne']

def edgeComponentWordLaw (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : Measure (Fin age → (Fin rule.edges × Bool)) :=
  (finiteWeightPMF (edgeComponentWordWeight rule marks fine age)
    (edgeComponentWordWeight_nonnegative rule marks fine age)
    (edgeComponentWordWeight_sum rule marks crossing fine age)).toMeasure

instance edgeComponentWordLaw_probability (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : IsProbabilityMeasure (edgeComponentWordLaw rule marks crossing fine age) := by
  unfold edgeComponentWordLaw
  infer_instance

/-- Actual edge allocation weights and the full counting allocation weights,
including both terminals and the old birth frontier, converge jointly. -/
theorem actual_joint_edge_counting_word_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        (∀ address opened, rule.network.crosses (marks (address, opened)) = opened) ∧
        (∀ address, 0 ≤ weight address marks) ∧
        (∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) marks = 1) ∧
        ∀ age (fallback word : Fin age → (Fin rule.edges × Bool)),
          Tendsto (fun fine => edgeComponentWordWeight rule marks fine age word) atTop
            (𝓝 (weight (List.ofFn word) marks)) ∧
          Tendsto (fun fine => fullComponentEmpiricalWordWeight rule marks fine age fallback word) atTop
            (𝓝 (weight (List.ofFn word) marks)) := by
  obtain ⟨weight, properties⟩ := actual_component_joint_edge_vertex_weights classicalRule p positive belowOne fixedPoint
  refine ⟨weight, ?_⟩
  filter_upwards [properties, independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint]
    with marks properties crossing growth
  refine ⟨crossing, fun address => (properties.2.1 address).1, properties.2.2, ?_⟩
  intro age fallback word
  constructor
  · simpa only [edgeComponentWordWeight, List.length_ofFn] using (properties.2.1 (List.ofFn word)).2.2
  · apply fullComponentEmpiricalWordWeight_tendsto rule marks growth (fun address => weight address marks)
    intro address
    exact (properties.2.1 address).2.1

theorem edge_counting_projection_tendsto_zero
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (limits : ∀ age (fallback word : Fin age → (Fin rule.edges × Bool)),
      Tendsto (fun fine => edgeComponentWordWeight rule marks fine age word) atTop (𝓝 (weight (List.ofFn word))) ∧
      Tendsto (fun fine => fullComponentEmpiricalWordWeight rule marks fine age fallback word) atTop (𝓝 (weight (List.ofFn word))))
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (anchor : ℕ → (Fin age → (Fin rule.edges × Bool)) → Space) :
    Tendsto (fun fine => levyProkhorovEDist
      ((edgeComponentWordLaw rule marks crossing fine age).map (anchor fine))
      ((fullComponentEmpiricalWordLaw rule marks crossing fine age fallback).map (anchor fine))) atTop (𝓝 0) := by
  have difference : Tendsto (fun fine => ∑ word : Fin age → (Fin rule.edges × Bool),
      |edgeComponentWordWeight rule marks fine age word -
        fullComponentEmpiricalWordWeight rule marks fine age fallback word|) atTop (𝓝 0) := by
    have result := tendsto_finsetSum Finset.univ (fun (word : Fin age → (Fin rule.edges × Bool)) _ =>
      ((limits age fallback word).1.sub (limits age fallback word).2).abs)
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using result
  have errorConvergence : Tendsto (fun fine => ∑ word : Fin age → (Fin rule.edges × Bool),
      ENNReal.ofReal |edgeComponentWordWeight rule marks fine age word -
        fullComponentEmpiricalWordWeight rule marks fine age fallback word|) atTop (𝓝 0) := by
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun word _ => abs_nonneg (_ - _))]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp difference
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds errorConvergence (fun _ => bot_le)
  intro fine
  exact levyProkhorovEDist_finiteWeightPMF_map_le
    (edgeComponentWordWeight rule marks fine age) (fullComponentEmpiricalWordWeight rule marks fine age fallback)
    (edgeComponentWordWeight_nonnegative rule marks fine age)
    (fullComponentEmpiricalWordWeight_nonnegative rule marks fine age fallback)
    (edgeComponentWordWeight_sum rule marks crossing fine age)
    (fullComponentEmpiricalWordWeight_sum rule marks crossing fine age fallback) (anchor fine) (measurable_of_finite _)

end
end IGSIII34.Diffusion
