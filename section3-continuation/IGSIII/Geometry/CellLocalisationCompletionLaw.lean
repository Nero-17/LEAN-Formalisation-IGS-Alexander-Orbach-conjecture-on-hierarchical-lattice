import IGSIII.Geometry.CellLocalisationGH

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory GromovHausdorff
open scoped ENNReal

/-- Every descendant has the same joint completed-space law. -/
theorem rootedCompletionFamily_descendant_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
    (familyMeasurable : Measurable family)
    (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks => family
        (innovationTreeShift rule address marks)) =
      (independentInnovationLaw rule p positive below_one fixed_point).map
        (family) := by
  change (independentInnovationLaw rule p positive below_one fixed_point).map
    (family ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (familyMeasurable)
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive below_one fixed_point address).map_eq]

/-- The joint completed C/N planted spaces at a genuine fixed-depth frontier are
independent; the two sides of a noncrossing mark are not resampled. -/
theorem rootedCompletionFamily_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
    (familyMeasurable : Measurable family)
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    iIndepFun (fun group marks => family
      (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive below_one fixed_point) :=
  (innovationFrontier_independent rule p positive below_one fixed_point addresses distinct depth same_length).comp
    (fun _ => family)
    (fun _ => familyMeasurable)

/-- The whole frontier family of completed compact spaces is independent of the
whole earlier innovation prefix, not merely pairwise independent of its marks. -/
theorem rootedCompletionFamily_prefix_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
    (familyMeasurable : Measurable family)
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) => marks coordinate.val)
      (fun marks group => family
        (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive below_one fixed_point) :=
  (innovationPrefix_frontier_independent rule p positive below_one fixed_point addresses distinct depth same_length).comp
    measurable_id (measurable_pi_lambda _ (fun group =>
      (familyMeasurable).comp (measurable_pi_apply group)))

/-- The exact joint distribution of the actual frontier completed compact spaces is the
product of their common completed-space law. -/
theorem rootedCompletionFamily_frontier_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
    (familyMeasurable : Measurable family)
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks group => family
        (innovationTreeShift rule (addresses group) marks)) =
      Measure.infinitePi (fun _ : Group =>
        (independentInnovationLaw rule p positive below_one fixed_point).map
          (family)) := by
  have joint_law := iIndepFun.map_fun_eq_infinitePi_map
    (fun group => (familyMeasurable).comp
      (innovationTreeShift_measurable rule (addresses group)))
    (rootedCompletionFamily_frontier_independent rule p positive below_one fixed_point family familyMeasurable
      addresses distinct depth same_length)
  simp only [Function.comp_def] at joint_law
  rw [joint_law]
  simp_rw [rootedCompletionFamily_descendant_law rule p positive below_one fixed_point family familyMeasurable]

/-- The exact conditional product law is encoded as independence from the
whole finite prefix together with the common product marginal. -/
theorem rootedCompletionFamily_prefix_frontier_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
    (familyMeasurable : Measurable family)
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks => ((fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        marks coordinate.val), fun group => family
          (innovationTreeShift rule (addresses group) marks))) =
      (Measure.infinitePi (fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        Rule.ConfigurationHistory.law rule p positive below_one fixed_point coordinate.val.2 0)).prod
      (Measure.infinitePi (fun _ : Group =>
        (independentInnovationLaw rule p positive below_one fixed_point).map
          (family))) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive below_one fixed_point coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive below_one fixed_point coordinate.2 0
  have joint_law := (rootedCompletionFamily_prefix_frontier_independent rule p positive below_one fixed_point family familyMeasurable
    addresses distinct depth same_length).map_prod_eq_prod_map_map
      (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)).aemeasurable
      (measurable_pi_lambda _ (fun group =>
        (familyMeasurable).comp
          (innovationTreeShift_measurable rule (addresses group)))).aemeasurable
  simp only [Function.comp_def] at joint_law
  rw [joint_law,
    rootedCompletionFamily_frontier_law rule p positive below_one fixed_point family familyMeasurable addresses distinct depth same_length]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective
end
end IGSIII.Geometry






