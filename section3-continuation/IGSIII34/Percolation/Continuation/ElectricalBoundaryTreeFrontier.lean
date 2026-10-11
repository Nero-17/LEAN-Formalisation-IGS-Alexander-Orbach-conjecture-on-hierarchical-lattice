import IGSIII34.Percolation.Continuation.ElectricalBoundaryTreeGraft

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

private theorem electricalBoundaryFrontierCoordinate_injective (rule : Rule) {Group : Type*}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
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

theorem electricalBoundaryTreeFrontier_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) {Group : Type*}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample group => electricalBoundaryTreeShift rule (addresses group) sample) =
        Measure.infinitePi (fun _ : Group => electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_map
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law:Measure ℝ≥0))
    (fun coordinate : (group : Group) × (List (Fin rule.edges) × Bool) =>
      (addresses coordinate.1 ++ coordinate.2.1, coordinate.2.2))
    (electricalBoundaryFrontierCoordinate_injective rule addresses distinct depth sameLength)

private def electricalBoundaryPrefixTailIndex (rule : Rule) (Group : Type) (depth : ℕ) : Bool → Type
  | false => {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}
  | true => Group × (List (Fin rule.edges) × Bool)

private def electricalBoundaryPrefixTailCoordinate (rule : Rule) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (depth : ℕ) :
    ((group : Bool) × electricalBoundaryPrefixTailIndex rule Group depth group) → List (Fin rule.edges) × Bool
  | ⟨false, coordinate⟩ => coordinate.val
  | ⟨true, group, address, opened⟩ => (addresses group ++ address, opened)

private theorem electricalBoundaryPrefixTailCoordinate_injective (rule : Rule) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    Function.Injective (electricalBoundaryPrefixTailCoordinate rule addresses depth) := by
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

theorem electricalBoundaryTree_marks_prefix_subtrees_independent (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) {Group : Type}
    (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
          (sample coordinate.val).1)
      (fun sample group => electricalBoundaryTreeShift rule (addresses group) sample)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law:Measure ℝ≥0))
    (electricalBoundaryPrefixTailCoordinate rule addresses depth)
    (electricalBoundaryPrefixTailCoordinate_injective rule addresses distinct depth sameLength)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  exact two.comp
    (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))
    (measurable_pi_lambda _ (fun group => measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (group, coordinate))))

theorem electricalBoundaryTree_frontier_iteration_map (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (outerDepth innerDepth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample leaf => electricalBoundaryTreeIteration rule innerDepth
        (electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample)) =
        Measure.pi (fun _ : Fin (rule.generation outerDepth).edges =>
          ((electricalOutputLaw rule p positive belowOne fixedPoint)^[innerDepth] law:Measure ℝ≥0)) := by
  change (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
    ((fun children : Fin (rule.generation outerDepth).edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
        fun leaf => electricalBoundaryTreeIteration rule innerDepth (children leaf)) ∘
      (fun sample leaf => electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample)) = _
  rw [← Measure.map_map
    (g := fun children : Fin (rule.generation outerDepth).edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
        fun leaf => electricalBoundaryTreeIteration rule innerDepth (children leaf))
    (f := fun sample leaf => electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample)
    (measurable_pi_lambda _ (fun leaf =>
      (electricalBoundaryTreeIteration_measurable rule innerDepth).comp (measurable_pi_apply leaf)))
    (measurable_pi_lambda _ (fun leaf =>
      electricalBoundaryTreeShift_measurable rule (generationEdgeAddress rule outerDepth leaf))),
    electricalBoundaryTreeFrontier_map rule p positive belowOne fixedPoint law
      (generationEdgeAddress rule outerDepth) (generationEdgeAddress_injective rule outerDepth)
      (outerDepth+1) (generationEdgeAddress_length rule outerDepth), Measure.infinitePi_eq_pi,
    Measure.pi_map_pi (fun _ => (electricalBoundaryTreeIteration_measurable rule innerDepth).aemeasurable)]
  simp only [electricalBoundaryTreeIteration_law]

end
end IGSIII34.Percolation
