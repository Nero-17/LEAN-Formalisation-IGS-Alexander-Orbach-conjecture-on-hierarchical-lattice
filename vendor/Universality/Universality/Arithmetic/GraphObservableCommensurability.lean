import Universality.Arithmetic.GraphCoreObservableExponents
import Universality.Arithmetic.GraphDimensionRank
import Universality.Arithmetic.GraphIteration
import Universality.Arithmetic.IrreducibleCommensurability
import Universality.Arithmetic.GraphWheatstoneArithmetic
import Universality.Arithmetic.GraphDiamondArithmetic

/-!
Section 4 conclusions from the actual crossing-length, escaping-mass and
critical-size logarithmic limits. Formula evidence is proved by the observable
interface, rather than supplied as a premise. Identification with the uniformly
rooted infinite graph's physical probability law remains a separate theorem.
-/

namespace Universality.Rule
noncomputable section
open Polynomial Matrix

theorem Classical.commensurate_of_coreObservableExponents_rank {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstLimits : first.CoreObservableExponents p firstExponents)
    (hsecondLimits : second.CoreObservableExponents q secondExponents)
    (hequal : firstExponents = secondExponents)
    (hrank : 3 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (first.criticalDimensionRankValues p)))) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) :=
  hfirst.commensurate_of_criticalDimension_rank hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.coreObservableExponents_eq_iff_criticalDimensions_eq hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond firstExponents secondExponents hfirstLimits hsecondLimits).mp hequal) hrank

theorem Classical.criticalDimension_rank_le_two_of_coreObservableExponents_not_commensurate {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstLimits : first.CoreObservableExponents p firstExponents)
    (hsecondLimits : second.CoreObservableExponents q secondExponents)
    (hequal : firstExponents = secondExponents)
    (hnot : ¬ ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target)) :
    Module.finrank ℚ
      (Submodule.span ℚ (Set.range (first.criticalDimensionRankValues p))) ≤ 2 :=
  hfirst.criticalDimension_rank_le_two_of_not_commensurate hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.coreObservableExponents_eq_iff_criticalDimensions_eq hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond firstExponents secondExponents hfirstLimits hsecondLimits).mp hequal) hnot

theorem Classical.commensurate_of_coreObservableExponents_irreducible {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstLimits : first.CoreObservableExponents p firstExponents)
    (hsecondLimits : second.CoreObservableExponents q secondExponents)
    (hequal : firstExponents = secondExponents)
    (hirreducible : Irreducible ((first.network.integerFixedPointPolynomial
      (hfirst.connected _)).map (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) :=
  hfirst.commensurate_of_irreducible_fixedPoint hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond
    ((hfirst.coreObservableExponents_eq_iff_criticalDimensions_eq hsecond p q hp hp' hq hq'
      hfixedFirst hfixedSecond firstExponents secondExponents hfirstLimits hsecondLimits).mp hequal) hirreducible hnonsplit

theorem Classical.common_primitive_base_of_coreObservableExponents_rank {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (exponents : ι → Fin 3 → ℝ)
    (hlimits : ∀ index, (rules index).CoreObservableExponents (criticalPoints index) (exponents index))
    (hcommon : ∀ index, exponents index = exponents reference)
    (hrank : 3 ≤ Module.finrank ℚ (Submodule.span ℚ
      (Set.range ((rules reference).criticalDimensionRankValues (criticalPoints reference))))) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  have hdimensions (index : ι) :
      (rules index).criticalDimensions (criticalPoints index) =
        (rules reference).criticalDimensions (criticalPoints reference) :=
    ((hclassical index).coreObservableExponents_eq_iff_criticalDimensions_eq
      (hclassical reference) (criticalPoints index) (criticalPoints reference)
      (hpositive index) (hless index) (hpositive reference) (hless reference)
      (hfixed index) (hfixed reference) (exponents index) (exponents reference)
      (hlimits index) (hlimits reference)).mp (hcommon index)
  exact Classical.common_primitive_base_of_criticalDimension_rank rules criticalPoints reference
    hclassical hpositive hless hfixed hdimensions hrank

theorem Classical.common_primitive_base_of_coreObservableExponents_irreducible {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (exponents : ι → Fin 3 → ℝ)
    (hlimits : ∀ index, (rules index).CoreObservableExponents (criticalPoints index) (exponents index))
    (hcommon : ∀ index, exponents index = exponents reference)
    (hirreducible : Irreducible (((rules reference).network.integerFixedPointPolynomial
      ((hclassical reference).connected _)).map (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ (((rules reference).network.massMatrix
      (criticalPoints reference)).map Complex.ofReal)).toReal ∉
        IntermediateField.adjoin ℚ {criticalPoints reference}) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  have hdimensions (index : ι) :
      (rules index).criticalDimensions (criticalPoints index) =
        (rules reference).criticalDimensions (criticalPoints reference) :=
    ((hclassical index).coreObservableExponents_eq_iff_criticalDimensions_eq
      (hclassical reference) (criticalPoints index) (criticalPoints reference)
      (hpositive index) (hless index) (hpositive reference) (hless reference)
      (hfixed index) (hfixed reference) (exponents index) (exponents reference)
      (hlimits index) (hlimits reference)).mp (hcommon index)
  exact Classical.common_primitive_base_of_irreducible_fixedPoint rules criticalPoints reference
    hclassical hpositive hless hfixed hdimensions hirreducible hnonsplit

theorem Classical.scale_log_rank_le_two_of_coreObservableExponents {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (exponents : ι → Fin 3 → ℝ)
    (hlimits : ∀ index, (rules index).CoreObservableExponents (criticalPoints index) (exponents index))
    (hcommon : ∀ index, exponents index = exponents reference)
    (dimensionIndex : Fin 3)
    (hirrational : Irrational
      ((rules reference).criticalDimensions (criticalPoints reference) dimensionIndex)) :
    Module.rank ℚ (Submodule.span ℚ (Set.range (fun index =>
      Real.log ((rules index).network.fullGraph.dist
        (rules index).network.source (rules index).network.target : ℝ)))) ≤ 2 := by
  have hdimensions (index : ι) :
      (rules index).criticalDimensions (criticalPoints index) =
        (rules reference).criticalDimensions (criticalPoints reference) :=
    ((hclassical index).coreObservableExponents_eq_iff_criticalDimensions_eq
      (hclassical reference) (criticalPoints index) (criticalPoints reference)
      (hpositive index) (hless index) (hpositive reference) (hless reference)
      (hfixed index) (hfixed reference) (exponents index) (exponents reference)
      (hlimits index) (hlimits reference)).mp (hcommon index)
  exact Classical.scale_log_rank_le_two_of_irrational_criticalDimension rules criticalPoints
    hclassical hpositive hless hfixed dimensionIndex _ hirrational
    (fun index => congrFun (hdimensions index) dimensionIndex)

theorem Classical.aligned_coreObservableExponents_iff {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstLimits : first.CoreObservableExponents p firstExponents)
    (hsecondLimits : second.CoreObservableExponents q secondExponents)
    (firstSteps secondSteps : ℕ) (hfirstSteps : 0 < firstSteps) (hsecondSteps : 0 < secondSteps)
    (haligned : first.network.fullGraph.dist first.network.source first.network.target ^ firstSteps =
      second.network.fullGraph.dist second.network.source second.network.target ^ secondSteps) :
    firstExponents = secondExponents ↔
      first.edges ^ firstSteps = second.edges ^ secondSteps ∧
      (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ^ firstSteps =
        (spectralRadius ℂ ((second.network.massMatrix q).map Complex.ofReal)).toReal ^ secondSteps ∧
      deriv first.network.reliability p ^ firstSteps =
        deriv second.network.reliability q ^ secondSteps :=
  (hfirst.coreObservableExponents_eq_iff_criticalDimensions_eq hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond firstExponents secondExponents hfirstLimits hsecondLimits).trans
      (hfirst.aligned_criticalDimensions_iff hsecond p q hp hp' hq hq'
        hfixedFirst hfixedSecond firstSteps secondSteps hfirstSteps hsecondSteps haligned)

theorem Classical.scale_power_two_of_wheatstone_coreObservableExponents {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (exponents : Fin 3 → ℝ)
    (hlimits : rule.CoreObservableExponents p exponents)
    (hwheatstoneLimits : wheatstoneRule.CoreObservableExponents (1 / 2) exponents) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  have hdimensions := (h.coreObservableExponents_eq_iff_criticalDimensions_eq
    wheatstoneRule_classical p (1 / 2) hp hp' (by norm_num) (by norm_num)
    hfixed wheatstone_reliability_half exponents exponents hlimits hwheatstoneLimits).mp rfl
  exact h.scale_power_two_of_wheatstone_dimensions p hp hp' hfixed
    (congrFun hdimensions 0) (congrFun hdimensions 2)

theorem Classical.scale_power_two_of_diamond_coreObservableExponents {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (exponents : Fin 3 → ℝ)
    (hlimits : rule.CoreObservableExponents p exponents)
    (hdiamondLimits : diamondRule.CoreObservableExponents diamondCriticalProbability exponents) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  have hdimensions := (h.coreObservableExponents_eq_iff_criticalDimensions_eq
    diamondRule_classical p diamondCriticalProbability hp hp'
    diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2
    hfixed diamond_critical_fixed_point exponents exponents hlimits hdiamondLimits).mp rfl
  exact h.scale_power_two_of_diamond_dimensions p hp hp' hfixed hdimensions

end
end Universality.Rule

#print axioms Universality.Rule.Classical.commensurate_of_coreObservableExponents_rank
#print axioms Universality.Rule.Classical.commensurate_of_coreObservableExponents_irreducible
#print axioms Universality.Rule.Classical.common_primitive_base_of_coreObservableExponents_rank
#print axioms Universality.Rule.Classical.common_primitive_base_of_coreObservableExponents_irreducible
#print axioms Universality.Rule.Classical.scale_log_rank_le_two_of_coreObservableExponents
#print axioms Universality.Rule.Classical.aligned_coreObservableExponents_iff
#print axioms Universality.Rule.Classical.scale_power_two_of_wheatstone_coreObservableExponents
#print axioms Universality.Rule.Classical.scale_power_two_of_diamond_coreObservableExponents
