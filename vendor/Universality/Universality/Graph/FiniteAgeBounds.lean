import Universality.Graph.FiniteAgeDisintegration
import Universality.Percolation.InternalClusterMassLimit

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

theorem interiorAgeFiber_isEmpty (rule : Rule) (depth age : ℕ) (hage : depth < age) :
    IsEmpty {vertex : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth vertex = age} := by
  refine ⟨fun vertex => ?_⟩
  have hle := rule.interiorVertexAge_le depth vertex.val
  rw [vertex.property] at hle
  omega

theorem finiteRootAgeProbability_eq_zero_of_lt (rule : Rule) (depth age : ℕ) (hage : depth < age) :
    rule.finiteRootAgeProbability depth age = 0 := by
  letI := rule.interiorAgeFiber_isEmpty depth age hage
  simp [finiteRootAgeProbability]

theorem ageRootClusterNumerator_eq_zero_of_lt (rule : Rule) (depth age : ℕ)
    (hage : depth < age) (p : ℝ) (size : ℕ) :
    rule.ageRootClusterNumerator depth age p size = 0 := by
  letI := rule.interiorAgeFiber_isEmpty depth age hage
  simp [ageRootClusterNumerator]

theorem finiteRootAgeProbability_nonneg (rule : Rule) (depth age : ℕ) :
    0 ≤ rule.finiteRootAgeProbability depth age := by
  unfold finiteRootAgeProbability
  positivity

/-- A summable domination obtained directly from the youngest age fibre's
inclusion in the actual vertex set. -/
theorem finiteRootAgeProbability_le_geometric (rule : Rule) (hedges : 1 < rule.edges)
    (depth age : ℕ) :
    rule.finiteRootAgeProbability depth age ≤ (1 / (rule.edges : ℝ)) ^ age := by
  have hm : 0 < (rule.edges : ℝ) := by exact_mod_cast (by omega : 0 < rule.edges)
  have hv : 0 < ((rule.generation depth).vertices : ℝ) := by
    exact_mod_cast (by have := (rule.generation depth).network.two_le_vertices; omega :
      0 < (rule.generation depth).vertices)
  by_cases hage : age ≤ depth
  · have hcard : Fintype.card {vertex : (rule.generation depth).network.InteriorVertex //
        rule.interiorVertexAge depth vertex = 0} ≤ (rule.generation depth).vertices := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (fun vertex : {vertex : (rule.generation depth).network.InteriorVertex //
          rule.interiorVertexAge depth vertex = 0} => vertex.val.val)
        (fun _ _ heq => Subtype.ext (Subtype.ext heq))
    rw [rule.card_interiorVertexAge depth 0 (Nat.zero_le depth), Nat.sub_zero] at hcard
    have hvolume : ((rule.vertices - 2 : ℕ) : ℝ) * (rule.edges : ℝ) ^ depth ≤
        (rule.generation depth).vertices := by exact_mod_cast hcard
    unfold finiteRootAgeProbability
    rw [rule.card_interiorVertexAge depth age hage, Nat.cast_mul, Nat.cast_pow, one_div_pow]
    apply (div_le_div_iff₀ hv (pow_pos hm age)).mpr
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hage, one_mul]
    exact hvolume
  · rw [rule.finiteRootAgeProbability_eq_zero_of_lt depth age (by omega)]
    positivity

theorem terminalRootClusterNumerator_bounds (rule : Rule) (depth : ℕ)
    (p : unitInterval) (size : ℕ) :
    0 ≤ rule.terminalRootClusterNumerator depth (p : ℝ) size ∧
      rule.terminalRootClusterNumerator depth (p : ℝ) size ≤ 2 := by
  have hweight := fun configuration : FiniteNetwork.Configuration (rule.generation depth).edges =>
    FiniteNetwork.bernoulliWeight_nonneg p.property.1 p.property.2 configuration
  constructor
  · unfold terminalRootClusterNumerator
    apply Finset.sum_nonneg
    intro configuration hconfiguration
    exact mul_nonneg (hweight configuration) (by positivity)
  · calc
      rule.terminalRootClusterNumerator depth (p : ℝ) size ≤
          ∑ configuration : FiniteNetwork.Configuration (rule.generation depth).edges,
            FiniteNetwork.bernoulliWeight (p : ℝ) configuration * 2 := by
        apply Finset.sum_le_sum
        intro configuration hconfiguration
        apply mul_le_mul_of_nonneg_left _ (hweight configuration)
        split_ifs <;> norm_num
      _ = 2 := by rw [← Finset.sum_mul, FiniteNetwork.sum_bernoulliWeight, one_mul]

theorem terminalRootClusterContribution_tendsto_zero (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : unitInterval) (size : ℕ) :
    Tendsto (fun depth => rule.terminalRootClusterNumerator depth (p : ℝ) size /
      (rule.generation depth).vertices) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun depth => div_nonneg (rule.terminalRootClusterNumerator_bounds depth p size).1 (Nat.cast_nonneg _))
    (fun depth => div_le_div_of_nonneg_right
      (rule.terminalRootClusterNumerator_bounds depth p size).2 (Nat.cast_nonneg _))
  simpa only [mul_one_div, mul_zero] using
    (rule.generation_inverse_volume_tendsto_zero hedges hvertices).const_mul 2

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem ageRootClusterContribution_bounds (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (depth age size : ℕ) (p : unitInterval) :
    0 ≤ rule.ageRootClusterNumerator depth age (p : ℝ) size / (rule.generation depth).vertices ∧
      rule.ageRootClusterNumerator depth age (p : ℝ) size / (rule.generation depth).vertices ≤
        (1 / (rule.edges : ℝ)) ^ age := by
  by_cases hage : age ≤ depth
  · have heq := rule.weightedAncestralStageClusterProbability age (depth - age) size p
    rw [Nat.add_sub_of_le hage] at heq
    rw [← heq]
    have hprob : (rule.ancestralSampleLaw age p).real
        {sample | rule.ancestralSampleStageClusterSize age (depth - age) sample = size} ≤ 1 := by
      simpa only [probReal_univ] using measureReal_mono
        (μ := rule.ancestralSampleLaw age p) (Set.subset_univ
          {sample | rule.ancestralSampleStageClusterSize age (depth - age) sample = size})
    exact ⟨mul_nonneg (rule.finiteRootAgeProbability_nonneg depth age) measureReal_nonneg,
      (mul_le_of_le_one_right (rule.finiteRootAgeProbability_nonneg depth age) hprob).trans
        (rule.finiteRootAgeProbability_le_geometric hedges depth age)⟩
  · rw [rule.ageRootClusterNumerator_eq_zero_of_lt depth age (by omega), zero_div]
    exact ⟨le_rfl, by positivity⟩

end
end Universality.Rule
