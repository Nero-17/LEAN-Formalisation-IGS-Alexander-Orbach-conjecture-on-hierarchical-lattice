import Universality.Percolation.PhysicalExponentClass
import Universality.Arithmetic.GraphDimensionRank
import Universality.Arithmetic.GraphIteration
import Universality.Arithmetic.IrreducibleCommensurability
import Universality.Arithmetic.GraphWheatstoneArithmetic
import Universality.Arithmetic.GraphDiamondArithmetic

/-!
Section 4 scale conclusions for the four actual critical exponents. The
Section 3 class theorem supplies the bridge to the three dimension coordinates;
the remaining proofs apply the already established arithmetic theorems.

The class uses four actual exponents in the order beta, nu, delta, eta. The
infinite-cluster and finite-size probabilities concern the constructed random
ancestral graph with independent Bernoulli edges. Their identification with
the actual finite-volume limits is proved upstream. Crossing and two-point
averages are the actual finite-generation observations of the manuscript.
No formula witness is assumed in these statements. General rooted-graph
local-weak convergence and local finiteness are separate object-level claims;
neither is asserted by a class name or by the wrappers below.
-/

namespace Universality.Rule
noncomputable section
open Polynomial Matrix

/-- The technical interior-root instance follows from the classical graph hypotheses. -/
theorem Classical.physical_interiorVertex_nonempty {rule : Rule} (h : rule.Classical) :
    Nonempty rule.network.InteriorVertex := by
  obtain ⟨vertex, hsource, htarget⟩ := Fin.exists_ne_and_ne_of_two_lt
    rule.network.source rule.network.target h.vertices_gt_two
  exact ⟨⟨vertex, hsource, htarget⟩⟩

/-- The edge-index type used by the physical probability space is nonempty. -/
theorem Classical.physical_edges_neZero {rule : Rule} (h : rule.Classical) :
    NeZero rule.edges := ⟨Nat.ne_of_gt h.edges_pos⟩

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem Classical.same_physical_class_iff_criticalDimensions {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q) :
    SameCriticalExponentUniversalityClass first second hfirst.edges_gt_one hsecond.edges_gt_one p q ↔
      first.criticalDimensions p = second.criticalDimensions q := by
  rw [hfirst.same_critical_exponent_class_iff_dimensions hsecond p q hp hp' hfixedFirst hq hq' hfixedSecond]
  constructor
  · rintro ⟨hambient, hmass, hpivotal⟩
    funext index
    fin_cases index
    · exact hambient
    · exact hmass
    · exact hpivotal
  · intro hequal
    exact ⟨congrFun hequal 0, congrFun hequal 1, congrFun hequal 2⟩

theorem Classical.commensurate_of_physicalClass_rank {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hsame : SameCriticalExponentUniversalityClass first second
      hfirst.edges_gt_one hsecond.edges_gt_one p q)
    (hrank : 3 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (first.criticalDimensionRankValues p)))) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) :=
  hfirst.commensurate_of_criticalDimension_rank hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.same_physical_class_iff_criticalDimensions hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond).mp hsame) hrank

theorem Classical.criticalDimension_rank_le_two_of_physicalClass_not_commensurate {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hsame : SameCriticalExponentUniversalityClass first second
      hfirst.edges_gt_one hsecond.edges_gt_one p q)
    (hnot : ¬ ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target)) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (first.criticalDimensionRankValues p))) ≤ 2 :=
  hfirst.criticalDimension_rank_le_two_of_not_commensurate hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.same_physical_class_iff_criticalDimensions hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond).mp hsame) hnot

theorem Classical.commensurate_of_physicalClass_irreducible {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hsame : SameCriticalExponentUniversalityClass first second
      hfirst.edges_gt_one hsecond.edges_gt_one p q)
    (hirreducible : Irreducible ((first.network.integerFixedPointPolynomial
      (hfirst.connected _)).map (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) :=
  hfirst.commensurate_of_irreducible_fixedPoint hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.same_physical_class_iff_criticalDimensions hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond).mp hsame) hirreducible hnonsplit

theorem Classical.common_primitive_base_of_physicalClass_rank {ι : Type*}
    (rules : ι → Rule) [∀ index, Nonempty (rules index).network.InteriorVertex]
    [∀ index, NeZero (rules index).edges] (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (hcommon : ∀ index, SameCriticalExponentUniversalityClass (rules index) (rules reference)
      (hclassical index).edges_gt_one (hclassical reference).edges_gt_one
      (criticalPoints index) (criticalPoints reference))
    (hrank : 3 ≤ Module.finrank ℚ (Submodule.span ℚ
      (Set.range ((rules reference).criticalDimensionRankValues (criticalPoints reference))))) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  have hdimensions (index : ι) :=
    ((hclassical index).same_physical_class_iff_criticalDimensions (hclassical reference)
      (criticalPoints index) (criticalPoints reference) (hpositive index) (hless index)
      (hpositive reference) (hless reference) (hfixed index) (hfixed reference)).mp (hcommon index)
  exact Classical.common_primitive_base_of_criticalDimension_rank rules criticalPoints reference
    hclassical hpositive hless hfixed hdimensions hrank

theorem Classical.common_primitive_base_of_physicalClass_irreducible {ι : Type*}
    (rules : ι → Rule) [∀ index, Nonempty (rules index).network.InteriorVertex]
    [∀ index, NeZero (rules index).edges] (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (hcommon : ∀ index, SameCriticalExponentUniversalityClass (rules index) (rules reference)
      (hclassical index).edges_gt_one (hclassical reference).edges_gt_one
      (criticalPoints index) (criticalPoints reference))
    (hirreducible : Irreducible (((rules reference).network.integerFixedPointPolynomial
      ((hclassical reference).connected _)).map (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ (((rules reference).network.massMatrix
      (criticalPoints reference)).map Complex.ofReal)).toReal ∉
        IntermediateField.adjoin ℚ {criticalPoints reference}) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  have hdimensions (index : ι) :=
    ((hclassical index).same_physical_class_iff_criticalDimensions (hclassical reference)
      (criticalPoints index) (criticalPoints reference) (hpositive index) (hless index)
      (hpositive reference) (hless reference) (hfixed index) (hfixed reference)).mp (hcommon index)
  exact Classical.common_primitive_base_of_irreducible_fixedPoint rules criticalPoints reference
    hclassical hpositive hless hfixed hdimensions hirreducible hnonsplit

theorem Classical.scale_log_rank_le_two_of_physicalClass {ι : Type*}
    (rules : ι → Rule) [∀ index, Nonempty (rules index).network.InteriorVertex]
    [∀ index, NeZero (rules index).edges] (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (hcommon : ∀ index, SameCriticalExponentUniversalityClass (rules index) (rules reference)
      (hclassical index).edges_gt_one (hclassical reference).edges_gt_one
      (criticalPoints index) (criticalPoints reference))
    (dimensionIndex : Fin 3)
    (hirrational : Irrational
      ((rules reference).criticalDimensions (criticalPoints reference) dimensionIndex)) :
    Module.rank ℚ (Submodule.span ℚ (Set.range (fun index =>
      Real.log ((rules index).network.fullGraph.dist
        (rules index).network.source (rules index).network.target : ℝ)))) ≤ 2 := by
  have hdimensions (index : ι) :=
    ((hclassical index).same_physical_class_iff_criticalDimensions (hclassical reference)
      (criticalPoints index) (criticalPoints reference) (hpositive index) (hless index)
      (hpositive reference) (hless reference) (hfixed index) (hfixed reference)).mp (hcommon index)
  exact Classical.scale_log_rank_le_two_of_irrational_criticalDimension rules criticalPoints
    hclassical hpositive hless hfixed dimensionIndex _ hirrational
    (fun index => congrFun (hdimensions index) dimensionIndex)

theorem Classical.aligned_physicalClass_iff {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstSteps secondSteps : ℕ) (hfirstSteps : 0 < firstSteps) (hsecondSteps : 0 < secondSteps)
    (haligned : first.network.fullGraph.dist first.network.source first.network.target ^ firstSteps =
      second.network.fullGraph.dist second.network.source second.network.target ^ secondSteps) :
    SameCriticalExponentUniversalityClass first second hfirst.edges_gt_one hsecond.edges_gt_one p q ↔
      first.edges ^ firstSteps = second.edges ^ secondSteps ∧
      (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ^ firstSteps =
        (spectralRadius ℂ ((second.network.massMatrix q).map Complex.ofReal)).toReal ^ secondSteps ∧
      deriv first.network.reliability p ^ firstSteps =
        deriv second.network.reliability q ^ secondSteps :=
  (hfirst.same_physical_class_iff_criticalDimensions hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond).trans
      (hfirst.aligned_criticalDimensions_iff hsecond p q hp hp' hq hq'
        hfixedFirst hfixedSecond firstSteps secondSteps hfirstSteps hsecondSteps haligned)

local instance : Nonempty wheatstoneRule.network.InteriorVertex :=
  wheatstoneRule_classical.physical_interiorVertex_nonempty
local instance : NeZero wheatstoneRule.edges := wheatstoneRule_classical.physical_edges_neZero
local instance : Nonempty diamondRule.network.InteriorVertex :=
  diamondRule_classical.physical_interiorVertex_nonempty
local instance : NeZero diamondRule.edges := diamondRule_classical.physical_edges_neZero

theorem Classical.scale_power_two_of_wheatstone_physicalClass {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hsame : SameCriticalExponentUniversalityClass rule wheatstoneRule
      h.edges_gt_one wheatstoneRule_classical.edges_gt_one p (1 / 2)) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  have hdimensions := (h.same_physical_class_iff_criticalDimensions
    wheatstoneRule_classical p (1 / 2) hp hp' (by norm_num) (by norm_num)
    hfixed wheatstone_reliability_half).mp hsame
  exact h.scale_power_two_of_wheatstone_dimensions p hp hp' hfixed
    (congrFun hdimensions 0) (congrFun hdimensions 2)

theorem Classical.scale_power_two_of_diamond_physicalClass {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hsame : SameCriticalExponentUniversalityClass rule diamondRule
      h.edges_gt_one diamondRule_classical.edges_gt_one p diamondCriticalProbability) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  have hdimensions := (h.same_physical_class_iff_criticalDimensions
    diamondRule_classical p diamondCriticalProbability hp hp'
    diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2
    hfixed diamond_critical_fixed_point).mp hsame
  exact h.scale_power_two_of_diamond_dimensions p hp hp' hfixed hdimensions

end
end Universality.Rule

#print axioms Universality.Rule.Classical.same_physical_class_iff_criticalDimensions
#print axioms Universality.Rule.Classical.commensurate_of_physicalClass_rank
#print axioms Universality.Rule.Classical.criticalDimension_rank_le_two_of_physicalClass_not_commensurate
#print axioms Universality.Rule.Classical.commensurate_of_physicalClass_irreducible
#print axioms Universality.Rule.Classical.common_primitive_base_of_physicalClass_rank
#print axioms Universality.Rule.Classical.common_primitive_base_of_physicalClass_irreducible
#print axioms Universality.Rule.Classical.scale_log_rank_le_two_of_physicalClass
#print axioms Universality.Rule.Classical.aligned_physicalClass_iff
#print axioms Universality.Rule.Classical.scale_power_two_of_wheatstone_physicalClass
#print axioms Universality.Rule.Classical.scale_power_two_of_diamond_physicalClass
