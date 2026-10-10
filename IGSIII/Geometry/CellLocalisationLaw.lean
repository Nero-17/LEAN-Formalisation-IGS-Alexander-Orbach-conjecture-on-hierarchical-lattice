import Mathlib.Probability.Independence.InfinitePi
import IGSIII.Geometry.ActualSkeletonMetric
import IGSIII.Geometry.CriticalChemicalLengths
import IGSIII.Chemical.ShortestLp
import IGSIII.Probability.IndependentPrefix

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution
open IGSIII.Probability MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- Actual simple paths, with the empty path only for disconnected pairs. -/
def graphDistanceFamily (graph : SimpleGraph Vertex) (first last : Vertex) : PathFamily (Sym2 Vertex) := by
  classical
  exact if reachable : graph.Reachable first last then graphPathFamily graph first last reachable
    else { paths := {∅}, nonempty := by simp }

theorem graphDistanceFamily_shortest (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ) (first last : Vertex) :
    (graphDistanceFamily graph first last).shortest cost = weightedDistance graph cost first last := by
  classical
  by_cases reachable : graph.Reachable first last
  · simp only [graphDistanceFamily, weightedDistance, dif_pos reachable]
  · simp only [graphDistanceFamily, weightedDistance, dif_neg reachable]
    obtain ⟨path, membership, minimum⟩ :=
      (PathFamily.exists_minimizer ({ paths := {∅}, nonempty := by simp } : PathFamily (Sym2 Vertex)) cost)
    have empty : path = ∅ := by simpa only [Finset.mem_singleton] using membership
    simpa only [empty, PathFamily.pathCost, Finset.sum_empty] using minimum

theorem weightedDistance_configuration_measurable {vertices edges : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (network : FiniteNetwork vertices edges) (configuration : Sample → Configuration edges)
    (configuration_measurable : Measurable configuration) (cost : Sample → Sym2 (Fin vertices) → ℝ)
    (cost_measurable : Measurable cost) (first last : Fin vertices) :
    Measurable (fun sample => weightedDistance (network.openGraph (configuration sample)) (cost sample) first last) := by
  have dispatched := (PathFamily.shortest_dispatch_measurable
    (fun state : Configuration edges => graphDistanceFamily (network.openGraph state) first last)).comp
    (configuration_measurable.prodMk cost_measurable)
  change Measurable (fun sample =>
    (graphDistanceFamily (network.openGraph (configuration sample)) first last).shortest (cost sample)) at dispatched
  simpa only [graphDistanceFamily_shortest] using dispatched

theorem indexedBondCost_measurable {vertices edges : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (network : FiniteNetwork vertices edges) (values : Sample → Fin edges → ℝ)
    (values_measurable : Measurable values) :
    Measurable (fun sample => indexedBondCost network (values sample)) := by
  classical
  apply measurable_pi_lambda
  intro bond
  unfold indexedBondCost
  split_ifs
  · exact (measurable_pi_apply _).comp values_measurable
  · exact measurable_const

/-- The entire actual C/N configuration tower and all finite weighted pair
metrics. Keeping both states in one code preserves their common innovations. -/
def ChemicalMetricCode (rule : Rule) :=
  (∀ _opened : Bool, ∀ depth, Configuration (rule.generation depth).edges) ×
    (∀ _opened : Bool, ∀ depth, Fin (rule.generation depth).vertices → Fin (rule.generation depth).vertices → ℝ)

instance chemicalMetricCodeMeasurableSpace (rule : Rule) : MeasurableSpace (ChemicalMetricCode rule) :=
  inferInstanceAs (MeasurableSpace
    ((∀ _opened : Bool, ∀ depth, Configuration (rule.generation depth).edges) ×
      (∀ _opened : Bool, ∀ depth, Fin (rule.generation depth).vertices → Fin (rule.generation depth).vertices → ℝ)))

def chemicalMetricCode (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ChemicalMetricCode rule :=
  ⟨fun opened depth => markedGenerationConfiguration rule marks depth [] opened,
    fun opened depth first last => weightedDistance
      ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] opened))
      (indexedBondCost (rule.generation depth).network (fun edge =>
        amplitude * chemicalField rule p positive below_one fixed_point value (generationEdgeAddress rule depth edge) marks /
          growth ^ (depth + 1))) first last⟩

theorem chemicalMetricCode_measurable (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point)) :
    Measurable (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value) := by
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ (fun opened => measurable_pi_lambda _ (fun depth =>
      markedGenerationConfiguration_measurable rule depth [] opened))
  · apply measurable_pi_lambda
    intro opened
    apply measurable_pi_lambda
    intro depth
    apply measurable_pi_lambda
    intro first
    apply measurable_pi_lambda
    intro last
    exact weightedDistance_configuration_measurable (rule.generation depth).network
      (fun marks => markedGenerationConfiguration rule marks depth [] opened)
      (markedGenerationConfiguration_measurable rule depth [] opened) _
      (indexedBondCost_measurable _ _ (measurable_pi_lambda _ (fun edge =>
        (measurable_const.mul (chemicalField_measurable rule p positive below_one fixed_point value
          (generationEdgeAddress rule depth edge))).div_const _))) first last

/-- Every descendant has the same complete metric-code law. -/
theorem chemicalMetricCode_descendant_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value
        (innovationTreeShift rule address marks)) =
      (independentInnovationLaw rule p positive below_one fixed_point).map
        (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value) := by
  change (independentInnovationLaw rule p positive below_one fixed_point).map
    (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (chemicalMetricCode_measurable rule p positive below_one fixed_point growth amplitude value)
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive below_one fixed_point address).map_eq]

/-- Complete C/N distance codes at a genuine fixed-depth frontier are
independent; the two sides of a noncrossing mark are not resampled. -/
theorem chemicalMetricCode_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    iIndepFun (fun group marks => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value
      (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive below_one fixed_point) :=
  (innovationFrontier_independent rule p positive below_one fixed_point addresses distinct depth same_length).comp
    (fun _ => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value)
    (fun _ => chemicalMetricCode_measurable rule p positive below_one fixed_point growth amplitude value)

/-- The whole frontier family of complete metric codes is independent of the
whole earlier innovation prefix, not merely pairwise independent of its marks. -/
theorem chemicalMetricCode_prefix_frontier_independent (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) => marks coordinate.val)
      (fun marks group => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value
        (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive below_one fixed_point) :=
  (innovationPrefix_frontier_independent rule p positive below_one fixed_point addresses distinct depth same_length).comp
    measurable_id (measurable_pi_lambda _ (fun group =>
      (chemicalMetricCode_measurable rule p positive below_one fixed_point growth amplitude value).comp (measurable_pi_apply group)))

/-- The exact joint distribution of the actual frontier metric codes is the
product of their common code law. -/
theorem chemicalMetricCode_frontier_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks group => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value
        (innovationTreeShift rule (addresses group) marks)) =
      Measure.infinitePi (fun _ : Group =>
        (independentInnovationLaw rule p positive below_one fixed_point).map
          (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value)) := by
  have joint_law := iIndepFun.map_fun_eq_infinitePi_map
    (fun group => (chemicalMetricCode_measurable rule p positive below_one fixed_point growth amplitude value).comp
      (innovationTreeShift_measurable rule (addresses group)))
    (chemicalMetricCode_frontier_independent rule p positive below_one fixed_point growth amplitude value
      addresses distinct depth same_length)
  simp only [Function.comp_def] at joint_law
  rw [joint_law]
  simp_rw [chemicalMetricCode_descendant_law]

/-- The exact conditional product law is encoded as independence from the
whole finite prefix together with the common product marginal. -/
theorem chemicalMetricCode_prefix_frontier_law (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (same_length : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (fun marks => ((fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        marks coordinate.val), fun group => chemicalMetricCode rule p positive below_one fixed_point growth amplitude value
          (innovationTreeShift rule (addresses group) marks))) =
      (Measure.infinitePi (fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        Rule.ConfigurationHistory.law rule p positive below_one fixed_point coordinate.val.2 0)).prod
      (Measure.infinitePi (fun _ : Group =>
        (independentInnovationLaw rule p positive below_one fixed_point).map
          (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value))) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive below_one fixed_point coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive below_one fixed_point coordinate.2 0
  have joint_law := (chemicalMetricCode_prefix_frontier_independent rule p positive below_one fixed_point growth amplitude value
    addresses distinct depth same_length).map_prod_eq_prod_map_map
      (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)).aemeasurable
      (measurable_pi_lambda _ (fun group =>
        (chemicalMetricCode_measurable rule p positive below_one fixed_point growth amplitude value).comp
          (innovationTreeShift_measurable rule (addresses group)))).aemeasurable
  simp only [Function.comp_def] at joint_law
  rw [joint_law,
    chemicalMetricCode_frontier_law rule p positive below_one fixed_point growth amplitude value addresses distinct depth same_length]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective
end
end IGSIII.Geometry




