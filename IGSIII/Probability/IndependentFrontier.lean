import IGSIII.Probability.IndependentTreeChildren

/-! Independent descendant subtrees at any level frontier. -/

set_option autoImplicit false

namespace IGSIII.Probability

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution

variable {Group : Type*}

private theorem frontierCoordinate_injective (rule : Rule) (addresses : Group → List (Fin rule.edges))
    (distinct : Function.Injective addresses) (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    Function.Injective (fun coordinate : (group : Group) × (List (Fin rule.edges) × Bool) =>
      (addresses coordinate.1 ++ coordinate.2.1, coordinate.2.2)) := by
  rintro ⟨firstGroup, firstAddress, firstState⟩ ⟨secondGroup, secondAddress, secondState⟩ equality
  have split := List.append_inj (congrArg Prod.fst equality)
    ((sameLength firstGroup).trans (sameLength secondGroup).symm)
  have groups := distinct split.1
  have states := congrArg Prod.snd equality
  cases groups
  cases split.2
  cases states
  rfl

theorem innovationFrontier_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks group => innovationTreeShift rule (addresses group) marks) =
      Measure.infinitePi (fun _ : Group => independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_map
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (fun coordinate : (group : Group) × (List (Fin rule.edges) × Bool) =>
      (addresses coordinate.1 ++ coordinate.2.1, coordinate.2.2))
    (frontierCoordinate_injective rule addresses distinct depth sameLength)

theorem innovationFrontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    iIndepFun (fun group => innovationTreeShift rule (addresses group))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0)
    (fun coordinate : (group : Group) × (List (Fin rule.edges) × Bool) =>
      (addresses coordinate.1 ++ coordinate.2.1, coordinate.2.2))
    (frontierCoordinate_injective rule addresses distinct depth sameLength)

end IGSIII.Probability
