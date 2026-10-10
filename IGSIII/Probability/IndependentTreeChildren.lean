import IGSIII.Probability.IndependentTreeShift
import IGSIII.Probability.IndependentSubfamilies

set_option autoImplicit false

namespace IGSIII.Probability

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution

private theorem childCoordinate_injective (rule : Rule) : Function.Injective
    (fun coordinate : (edge : Fin rule.edges) × (List (Fin rule.edges) × Bool) =>
      (coordinate.1 :: coordinate.2.1, coordinate.2.2)) := by
  rintro ⟨firstEdge, firstAddress, firstState⟩ ⟨secondEdge, secondAddress, secondState⟩ equality
  have addresses := congrArg Prod.fst equality
  have states := congrArg Prod.snd equality
  have parts := List.cons.inj addresses
  cases parts.1
  cases parts.2
  cases states
  rfl

theorem innovationTreeChildren_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks edge => innovationTreeShift rule [edge] marks) =
      Measure.infinitePi (fun _ : Fin rule.edges =>
        independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_map
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (fun coordinate : (edge : Fin rule.edges) × (List (Fin rule.edges) × Bool) =>
      (coordinate.1 :: coordinate.2.1, coordinate.2.2)) (childCoordinate_injective rule)

theorem innovationTreeChildren_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    iIndepFun (fun edge => innovationTreeShift rule [edge])
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (fun coordinate : (edge : Fin rule.edges) × (List (Fin rule.edges) × Bool) =>
      (coordinate.1 :: coordinate.2.1, coordinate.2.2)) (childCoordinate_injective rule)

private def rootTailIndex (rule : Rule) : Bool → Type
  | false => Bool
  | true => Fin rule.edges × (List (Fin rule.edges) × Bool)

private def rootTailCoordinate (rule : Rule) :
    ((group : Bool) × rootTailIndex rule group) → List (Fin rule.edges) × Bool
  | ⟨false, opened⟩ => ([], opened)
  | ⟨true, edge, address, opened⟩ => (edge :: address, opened)

private theorem rootTailCoordinate_injective (rule : Rule) :
    Function.Injective (rootTailCoordinate rule) := by
  rintro ⟨firstGroup, first⟩ ⟨secondGroup, second⟩ equality
  cases firstGroup <;> cases secondGroup
  · have states := congrArg Prod.snd equality
    cases states
    rfl
  · have addresses := congrArg Prod.fst equality
    cases addresses
  · have addresses := congrArg Prod.fst equality
    cases addresses
  · rcases first with ⟨firstEdge, firstAddress, firstState⟩
    rcases second with ⟨secondEdge, secondAddress, secondState⟩
    have addresses := congrArg Prod.fst equality
    have states := congrArg Prod.snd equality
    have parts := List.cons.inj addresses
    cases parts.1
    cases parts.2
    cases states
    rfl

theorem innovationTreeRoot_children_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    IndepFun (fun marks => marks ([], opened))
      (fun marks edge => innovationTreeShift rule [edge] marks)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (rootTailCoordinate rule) (rootTailCoordinate_injective rule)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  exact two.comp (measurable_pi_apply opened)
    (measurable_pi_lambda _ (fun edge => measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (edge, coordinate))))

theorem innovationTreeRoot_children_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => (marks ([], opened), fun edge => innovationTreeShift rule [edge] marks)) =
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint opened 0).prod
        (Measure.infinitePi (fun _ : Fin rule.edges =>
          independentInnovationLaw rule p positive belowOne fixedPoint)) := by
  rw [(innovationTreeRoot_children_independent rule p positive belowOne fixedPoint opened).map_prod_eq_prod_map_map
    (measurable_pi_apply ([], opened)).aemeasurable
    (measurable_pi_lambda _ (fun edge => innovationTreeShift_measurable rule [edge])).aemeasurable,
    independentInnovationLaw_marginal, innovationTreeChildren_map]

end IGSIII.Probability
