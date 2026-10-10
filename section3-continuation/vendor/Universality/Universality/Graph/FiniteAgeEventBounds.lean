import Universality.Graph.FiniteAgeEventDisintegration
import Universality.Graph.FiniteAgeBounds

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

theorem ageRootEventNumerator_eq_zero_of_lt (rule : Rule)
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop)
    (depth age : ℕ) (hage : depth < age) (p : ℝ) :
    rule.ageRootEventNumerator event depth age p = 0 := by
  letI := rule.interiorAgeFiber_isEmpty depth age hage
  simp [ageRootEventNumerator]

theorem terminalRootEventNumerator_bounds (rule : Rule)
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop) (depth : ℕ)
    (p : unitInterval) :
    0 ≤ rule.terminalRootEventNumerator event depth (p : ℝ) ∧
      rule.terminalRootEventNumerator event depth (p : ℝ) ≤ 2 := by
  have hweight := fun configuration : FiniteNetwork.Configuration (rule.generation depth).edges =>
    FiniteNetwork.bernoulliWeight_nonneg p.property.1 p.property.2 configuration
  constructor
  · unfold terminalRootEventNumerator
    apply Finset.sum_nonneg
    intro configuration hconfiguration
    exact mul_nonneg (hweight configuration) (by positivity)
  · calc
      rule.terminalRootEventNumerator event depth (p : ℝ) ≤
          ∑ configuration : FiniteNetwork.Configuration (rule.generation depth).edges,
            FiniteNetwork.bernoulliWeight (p : ℝ) configuration * 2 := by
        apply Finset.sum_le_sum
        intro configuration hconfiguration
        apply mul_le_mul_of_nonneg_left _ (hweight configuration)
        split_ifs <;> norm_num
      _ = 2 := by rw [← Finset.sum_mul, FiniteNetwork.sum_bernoulliWeight, one_mul]

theorem terminalRootEventContribution_tendsto_zero (rule : Rule)
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : unitInterval) :
    Tendsto (fun depth => rule.terminalRootEventNumerator event depth (p : ℝ) /
      (rule.generation depth).vertices) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun depth => div_nonneg (rule.terminalRootEventNumerator_bounds event depth p).1 (Nat.cast_nonneg _))
    (fun depth => div_le_div_of_nonneg_right
      (rule.terminalRootEventNumerator_bounds event depth p).2 (Nat.cast_nonneg _))
  simpa only [mul_one_div, mul_zero] using
    (rule.generation_inverse_volume_tendsto_zero hedges hvertices).const_mul 2

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem ageRootEventContribution_bounds (rule : Rule)
    (event : ∀ depth, Fin (rule.generation depth).vertices →
      FiniteNetwork.Configuration (rule.generation depth).edges → Prop)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (depth age : ℕ) (p : unitInterval) :
    0 ≤ rule.ageRootEventNumerator event depth age (p : ℝ) / (rule.generation depth).vertices ∧
      rule.ageRootEventNumerator event depth age (p : ℝ) / (rule.generation depth).vertices ≤
        (1 / (rule.edges : ℝ)) ^ age := by
  by_cases hage : age ≤ depth
  · have heq := rule.weightedAncestralStageEventProbability event age (depth - age) p
    rw [Nat.add_sub_of_le hage] at heq
    rw [← heq]
    have hprob : (rule.ancestralSampleLaw age p).real
        {sample | sample ∈ rule.ancestralStageEvent event age (depth - age)} ≤ 1 := by
      simpa only [probReal_univ] using measureReal_mono
        (μ := rule.ancestralSampleLaw age p) (Set.subset_univ
          {sample | sample ∈ rule.ancestralStageEvent event age (depth - age)})
    exact ⟨mul_nonneg (rule.finiteRootAgeProbability_nonneg depth age) measureReal_nonneg,
      (mul_le_of_le_one_right (rule.finiteRootAgeProbability_nonneg depth age) hprob).trans
        (rule.finiteRootAgeProbability_le_geometric hedges depth age)⟩
  · rw [rule.ageRootEventNumerator_eq_zero_of_lt event depth age (by omega), zero_div]
    exact ⟨le_rfl, by positivity⟩

end
end Universality.Rule
