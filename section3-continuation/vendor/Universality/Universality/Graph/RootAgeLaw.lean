import Universality.Graph.BirthAgeLimit
import Mathlib.Probability.Distributions.Geometric

namespace Universality.Rule
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def rootAgeParameter (rule : Rule) (hedges : 1 < rule.edges) : unitInterval :=
  ⟨((rule.edges : ℝ) - 1) / rule.edges, by
    have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
    exact ⟨(div_pos (sub_pos.mpr hm) (lt_trans zero_lt_one hm)).le,
      (div_le_one (lt_trans zero_lt_one hm)).mpr (by linarith)⟩⟩

theorem rootAgeParameter_ne_zero (rule : Rule) (hedges : 1 < rule.edges) :
    rule.rootAgeParameter hedges ≠ 0 := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  intro heq
  have hval := congrArg (fun p : unitInterval => (p : ℝ)) heq
  change ((rule.edges : ℝ) - 1) / rule.edges = 0 at hval
  exact (ne_of_gt (div_pos (sub_pos.mpr hm) (lt_trans zero_lt_one hm))) hval

/-- The probability measure whose atoms are the independently proved limits
of actual finite uniform-root age probabilities. -/
def rootAgeLaw (rule : Rule) (hedges : 1 < rule.edges) : Measure ℕ :=
  geometricMeasure (rule.rootAgeParameter hedges)

instance rootAgeLaw_probability (rule : Rule) (hedges : 1 < rule.edges) :
    IsProbabilityMeasure (rule.rootAgeLaw hedges) := by
  unfold rootAgeLaw
  infer_instance

theorem rootAgeLaw_real_singleton (rule : Rule) (hedges : 1 < rule.edges) (age : ℕ) :
    (rule.rootAgeLaw hedges).real {age} =
      ((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1) := by
  have hm : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast (by omega : rule.edges ≠ 0)
  rw [rootAgeLaw, geometricMeasure_real_singleton (rule.rootAgeParameter_ne_zero hedges)]
  change (1 - ((rule.edges : ℝ) - 1) / rule.edges) ^ age *
    (((rule.edges : ℝ) - 1) / rule.edges) = _
  have heq : 1 - ((rule.edges : ℝ) - 1) / rule.edges = 1 / rule.edges := by
    field_simp [hm] <;> ring
  rw [heq, one_div_pow, pow_succ]
  field_simp [hm] <;> ring

theorem finiteRootAgeProbability_tendsto_rootAgeLaw (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (age : ℕ) :
    Tendsto (fun depth => rule.finiteRootAgeProbability depth age) atTop
      (𝓝 ((rule.rootAgeLaw hedges).real {age})) := by
  rw [rule.rootAgeLaw_real_singleton hedges age]
  exact rule.finiteRootAgeProbability_tendsto hedges hvertices age

end
end Universality.Rule
