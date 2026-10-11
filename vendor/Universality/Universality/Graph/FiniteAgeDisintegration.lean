import Universality.Graph.FiniteBernoulliMeasure
import Universality.Graph.AncestralStageJointLaw
import Universality.Graph.BirthAgeLimit

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem sum_vertices_terminal_interior {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (function : Fin vertices → ℝ) :
    (∑ vertex, function vertex) = function network.source + function network.target +
      ∑ vertex : network.InteriorVertex, function vertex.val := by
  have hterminal : (Finset.univ.filter (fun vertex : Fin vertices =>
      ¬ (vertex ≠ network.source ∧ vertex ≠ network.target))) =
        {network.source, network.target} := by
    ext vertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun vertex : Fin vertices => vertex ≠ network.source ∧ vertex ≠ network.target) function
  rw [hterminal] at hsplit
  rw [Finset.sum_subtype (p := fun vertex => vertex ≠ network.source ∧ vertex ≠ network.target)
    (F := (inferInstance : Fintype network.InteriorVertex))
    _ (fun vertex => by simp) function] at hsplit
  simpa only [Finset.sum_pair network.terminals_distinct, add_comm, InteriorVertex] using hsplit.symm

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

theorem sum_generation_vertices_by_age (rule : Rule) (depth : ℕ)
    (function : Fin (rule.generation depth).vertices → ℝ) :
    (∑ vertex, function vertex) =
      function (rule.generation depth).network.source +
      function (rule.generation depth).network.target +
      ∑ age ∈ Finset.range (depth + 1),
        ∑ vertex : {vertex : (rule.generation depth).network.InteriorVertex //
          rule.interiorVertexAge depth vertex = age}, function vertex.val.val := by
  rw [(rule.generation depth).network.sum_vertices_terminal_interior]
  congr 1
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (rule.generation depth).network.InteriorVertex))
    (t := Finset.range (depth + 1)) (g := rule.interiorVertexAge depth)
    (fun vertex _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (rule.interiorVertexAge_le depth vertex)))
    (fun vertex => function vertex.val)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro age hage
  exact Finset.sum_subtype (p := fun vertex => rule.interiorVertexAge depth vertex = age)
    _ (fun vertex => by simp)
      (fun vertex : (rule.generation depth).network.InteriorVertex => function vertex.val)

def ageRootClusterNumerator (rule : Rule) (depth age : ℕ) (p : ℝ) (size : ℕ) : ℝ :=
  ∑ configuration, FiniteNetwork.bernoulliWeight p configuration *
    ∑ vertex : {vertex : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth vertex = age},
      if ((rule.generation depth).network.clusterVertices configuration vertex.val.val).card = size
        then (1 : ℝ) else 0

def terminalRootClusterNumerator (rule : Rule) (depth : ℕ) (p : ℝ) (size : ℕ) : ℝ :=
  ∑ configuration, FiniteNetwork.bernoulliWeight p configuration *
    ((if ((rule.generation depth).network.clusterVertices configuration
      (rule.generation depth).network.source).card = size then (1 : ℝ) else 0) +
    (if ((rule.generation depth).network.clusterVertices configuration
      (rule.generation depth).network.target).card = size then (1 : ℝ) else 0))

/-- Exact disintegration of the original finite-volume expression, including
both exceptional terminal roots. -/
theorem uniformVertexClusterProbability_by_age (rule : Rule) (depth : ℕ) (p : ℝ) (size : ℕ) :
    (rule.generation depth).network.uniformVertexClusterMassProbability p size =
      rule.terminalRootClusterNumerator depth p size / (rule.generation depth).vertices +
        ∑ age ∈ Finset.range (depth + 1),
          rule.ageRootClusterNumerator depth age p size / (rule.generation depth).vertices := by
  unfold FiniteNetwork.uniformVertexClusterMassProbability terminalRootClusterNumerator
    ageRootClusterNumerator
  simp_rw [rule.sum_generation_vertices_by_age depth, mul_add]
  rw [Finset.sum_add_distrib, add_div]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem ancestralStageClusterSize_real_eq (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n size : ℕ) (p : unitInterval) :
    (rule.ancestralSampleLaw age p).real
        {sample | rule.ancestralSampleStageClusterSize age n sample = size} =
      rule.ageRootClusterNumerator (age + n) age (p : ℝ) size /
        Fintype.card (rule.AncestralAgeFiber age n) := by
  have h := congrArg ENNReal.toReal (rule.ancestralStageClusterSize_probability age n size p)
  change (rule.ancestralSampleLaw age p).real _ =
    ((rule.ancestralAgeFiberRootLaw age n).prod
      (Measure.pi (fun _ : Fin (rule.generation (age + n)).edges =>
        bernoulliMeasure true false p))).real _ at h
  rw [h]
  unfold ancestralAgeFiberRootLaw ageRootClusterNumerator
  convert Universality.mappedFiniteUniformBernoulli_event
    (fun vertex : rule.AncestralAgeFiber age n => vertex.val.val) (measurable_of_countable _)
    (rule.generation (age + n)).edges p
    (fun vertex configuration =>
      ((rule.generation (age + n)).network.clusterVertices configuration vertex).card = size)
    ((Set.to_countable _).measurableSet) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro configuration hconfiguration
  congr 1
  apply Finset.sum_congr rfl
  intro vertex hvertex
  split_ifs <;> rfl

theorem weightedAncestralStageClusterProbability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (age n size : ℕ) (p : unitInterval) :
    rule.finiteRootAgeProbability (age + n) age *
      (rule.ancestralSampleLaw age p).real
        {sample | rule.ancestralSampleStageClusterSize age n sample = size} =
      rule.ageRootClusterNumerator (age + n) age (p : ℝ) size /
        (rule.generation (age + n)).vertices := by
  rw [rule.ancestralStageClusterSize_real_eq]
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
