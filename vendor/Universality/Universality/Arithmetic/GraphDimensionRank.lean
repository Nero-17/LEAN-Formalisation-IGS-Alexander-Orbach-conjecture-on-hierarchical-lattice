import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Arithmetic.DimensionRank
import Universality.Arithmetic.CommonPrimitiveBase
import Universality.Arithmetic.ScaleLogRank

/-!
# Six-exponentials rigidity for the actual graph dimension formulas

Algebraicity of all six exponentials is discharged from the graph polynomial
and matrix definitions.  The only non-foundational axiom in the main theorem
is the separately declared six exponentials theorem.
-/

namespace Universality.Rule
noncomputable section

/-- The rational span in Section 4 includes `1` as well as all three critical
growth dimensions. -/
def criticalDimensionRankValues (rule : Rule) (p : ℝ) : Fin 4 → ℝ :=
  ![1, rule.criticalDimensions p 0, rule.criticalDimensions p 1, rule.criticalDimensions p 2]

theorem criticalDimensionRankValues_eq_of_dimensions_eq {first second : Rule}
    {p q : ℝ} (hequal : first.criticalDimensions p = second.criticalDimensions q) :
    first.criticalDimensionRankValues p = second.criticalDimensionRankValues q := by
  simp only [criticalDimensionRankValues, hequal]

theorem Classical.exp_log_scale_criticalDimensionRankValues_algebraic {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (index : Fin 4) :
    IsAlgebraic ℚ (Real.exp
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) *
        rule.criticalDimensionRankValues p index)) := by
  fin_cases index
  · change IsAlgebraic ℚ (Real.exp
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) * 1))
    rw [mul_one, Real.exp_log (by exact_mod_cast (lt_trans Nat.zero_lt_one h.scale))]
    exact isAlgebraic_nat _
  · exact h.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixed 0
  · exact h.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixed 1
  · exact h.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixed 2

/-- The rank hypothesis is on the actual dimensions of the first graph.
Equality with the second graph supplies the second algebraic-exponential row. -/
theorem Classical.commensurate_of_criticalDimension_rank {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hequal : first.criticalDimensions p = second.criticalDimensions q)
    (hrank : 3 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (first.criticalDimensionRankValues p)))) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) := by
  apply Section4.commensurate_of_dimension_rank hfirst.scale hsecond.scale
    (first.criticalDimensionRankValues p) hrank
  · exact hfirst.exp_log_scale_criticalDimensionRankValues_algebraic p hp hp' hfixedFirst
  · rw [criticalDimensionRankValues_eq_of_dimensions_eq hequal]
    exact hsecond.exp_log_scale_criticalDimensionRankValues_algebraic q hq hq' hfixedSecond

/-- Consequently, any equal-dimension pair on incommensurate integer scales
has rational span of `{1,D_H,D_f,D_p}` of dimension at most two. -/
theorem Classical.criticalDimension_rank_le_two_of_not_commensurate {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hequal : first.criticalDimensions p = second.criticalDimensions q)
    (hnot : ¬ ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target)) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (first.criticalDimensionRankValues p))) ≤ 2 := by
  by_contra hrank
  exact hnot (hfirst.commensurate_of_criticalDimension_rank hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond hequal (by omega))

/-- The common primitive base works for an arbitrary family of actual
classical graph rules, including infinite families. One representative supplies
the rank hypothesis, and all other representatives have the same three
critical finite-growth dimensions. -/
theorem Classical.common_primitive_base_of_criticalDimension_rank {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (hcommon : ∀ index, (rules index).criticalDimensions (criticalPoints index) =
      (rules reference).criticalDimensions (criticalPoints reference))
    (hrank : 3 ≤ Module.finrank ℚ (Submodule.span ℚ
      (Set.range ((rules reference).criticalDimensionRankValues (criticalPoints reference))))) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  letI : Nonempty ι := ⟨reference⟩
  have hreference (index : ι) :=
    (hclassical reference).commensurate_of_criticalDimension_rank (hclassical index)
      (criticalPoints reference) (criticalPoints index)
      (hpositive reference) (hless reference) (hpositive index) (hless index)
      (hfixed reference) (hfixed index) (hcommon index).symm hrank
  apply Section4.common_primitive_integer_base
    (fun index => (rules index).network.fullGraph.dist
      (rules index).network.source (rules index).network.target)
    (fun index => (hclassical index).scale)
  intro first second
  exact (hreference first).symm.trans (hreference second)

/-- A single common irrational critical dimension bounds the cardinal rank of
all scale logarithms by two. This does not assume that the family is finite
or that its scale-log span was already finite-dimensional. -/
theorem Classical.scale_log_rank_le_two_of_irrational_criticalDimension {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (dimensionIndex : Fin 3) (dimension : ℝ) (hirrational : Irrational dimension)
    (hcommon : ∀ index, (rules index).criticalDimensions (criticalPoints index) dimensionIndex = dimension) :
    Module.rank ℚ (Submodule.span ℚ (Set.range (fun index =>
      Real.log ((rules index).network.fullGraph.dist
        (rules index).network.source (rules index).network.target : ℝ)))) ≤ 2 := by
  apply Section4.scale_log_rank_le_two hirrational
    (fun index => (rules index).network.fullGraph.dist
      (rules index).network.source (rules index).network.target)
    (fun index => (hclassical index).scale)
  intro index
  rw [← hcommon index]
  exact (hclassical index).exp_log_scale_criticalDimensions_algebraic
    (criticalPoints index) (hpositive index) (hless index) (hfixed index) dimensionIndex

end
end Universality.Rule

#print axioms Universality.Rule.Classical.commensurate_of_criticalDimension_rank
#print axioms Universality.Rule.Classical.criticalDimension_rank_le_two_of_not_commensurate
#print axioms Universality.Rule.Classical.common_primitive_base_of_criticalDimension_rank
#print axioms Universality.Rule.Classical.scale_log_rank_le_two_of_irrational_criticalDimension
