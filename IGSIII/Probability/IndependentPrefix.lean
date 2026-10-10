import IGSIII.Probability.IndependentFrontier

/-! The whole finite prefix is independent of the complete frontier subtree family. -/

set_option autoImplicit false

namespace IGSIII.Probability

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution

private def prefixTailIndex (rule : Rule) (Group : Type) (depth : ℕ) : Bool → Type
  | false => {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}
  | true => Group × (List (Fin rule.edges) × Bool)

private def prefixTailCoordinate (rule : Rule) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (depth : ℕ) :
    ((group : Bool) × prefixTailIndex rule Group depth group) → List (Fin rule.edges) × Bool
  | ⟨false, coordinate⟩ => coordinate.val
  | ⟨true, group, address, opened⟩ => (addresses group ++ address, opened)

private theorem prefixTailCoordinate_injective (rule : Rule) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    Function.Injective (prefixTailCoordinate rule addresses depth) := by
  rintro ⟨firstGroup, first⟩ ⟨secondGroup, second⟩ equality
  cases firstGroup <;> cases secondGroup
  · have same : first.val = second.val := equality
    cases Subtype.ext same
    rfl
  · change first.val = (addresses second.1 ++ second.2.1, second.2.2) at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    simp only [List.length_append, sameLength] at lengths
    have short := first.property
    omega
  · change (addresses first.1 ++ first.2.1, first.2.2) = second.val at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    simp only [List.length_append, sameLength] at lengths
    have short := second.property
    omega
  · rcases first with ⟨firstIndex, firstAddress, firstState⟩
    rcases second with ⟨secondIndex, secondAddress, secondState⟩
    have split := List.append_inj (congrArg Prod.fst equality)
      ((sameLength firstIndex).trans (sameLength secondIndex).symm)
    have groups := distinct split.1
    have states := congrArg Prod.snd equality
    cases groups
    cases split.2
    cases states
    rfl

theorem innovationPrefix_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) =>
        marks coordinate.val)
      (fun marks group => innovationTreeShift rule (addresses group) marks)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (prefixTailCoordinate rule addresses depth)
    (prefixTailCoordinate_injective rule addresses distinct depth sameLength)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  exact two.comp measurable_id
    (measurable_pi_lambda _ (fun group => measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (group, coordinate))))

theorem innovationPrefix_frontier_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => ((fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
          marks coordinate.val), fun group => innovationTreeShift rule (addresses group) marks)) =
      (Measure.infinitePi (fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.val.2 0)).prod
      (Measure.infinitePi (fun _ : Group => independentInnovationLaw rule p positive belowOne fixedPoint)) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  rw [(innovationPrefix_frontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)).aemeasurable
    (measurable_pi_lambda _ (fun group => innovationTreeShift_measurable rule (addresses group))).aemeasurable,
    innovationFrontier_map rule p positive belowOne fixedPoint addresses distinct depth sameLength]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective

end IGSIII.Probability

