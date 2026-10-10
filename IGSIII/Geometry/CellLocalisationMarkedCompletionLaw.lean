import IGSIII.Geometry.CellLocalisationLaw
import IGSIII.Geometry.CellLocalisationCriticalLaw

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory GromovHausdorff
open scoped ENNReal

/-- A genuine completed compact-space family together with every original
configuration label and every finite vertex-labelled skeleton distance. -/
def MarkedChemicalCompletionCode (rule : Rule) :=
  ChemicalMetricCode rule × (Bool → Bool → GHSpace)

instance markedChemicalCompletionCodeMeasurableSpace (rule : Rule) :
    MeasurableSpace (MarkedChemicalCompletionCode rule) :=
  inferInstanceAs (MeasurableSpace (ChemicalMetricCode rule × (Bool → Bool → GHSpace)))

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
variable (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
variable (family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace)
variable (familyMeasurable : Measurable family)

def markedChemicalCompletionCode
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : MarkedChemicalCompletionCode rule :=
  (chemicalMetricCode rule p positive belowOne fixedPoint growth amplitude value marks, family marks)

include familyMeasurable

theorem markedChemicalCompletionCode_measurable :
    Measurable (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family) :=
  (chemicalMetricCode_measurable rule p positive belowOne fixedPoint growth amplitude value).prodMk familyMeasurable

theorem markedChemicalCompletionCode_descendant_law (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family
        (innovationTreeShift rule address marks)) =
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family) := by
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map
    (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable)
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq]

/-- Conditional independence retains all skeleton labels and all four actual
completed planted spaces in a single sample at each socket. In particular the
two noncrossing components are coupled through their original innovations. -/
theorem markedChemicalCompletionCode_frontier_independent
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    iIndepFun (fun group marks => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family
      (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (innovationFrontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    (fun _ => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family)
    (fun _ => markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable)

theorem markedChemicalCompletionCode_prefix_frontier_independent
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) => marks coordinate.val)
      (fun marks group => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family
        (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (innovationPrefix_frontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    measurable_id (measurable_pi_lambda _ (fun group =>
      (markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable).comp
        (measurable_pi_apply group)))

theorem markedChemicalCompletionCode_frontier_law
    {Group : Type*} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks group => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family
        (innovationTreeShift rule (addresses group) marks)) =
    Measure.infinitePi (fun _ : Group => (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family)) := by
  have jointLaw := iIndepFun.map_fun_eq_infinitePi_map
    (fun group => (markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable).comp
      (innovationTreeShift_measurable rule (addresses group)))
    (markedChemicalCompletionCode_frontier_independent rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable
      addresses distinct depth sameLength)
  simp only [Function.comp_def] at jointLaw
  rw [jointLaw]
  simp_rw [markedChemicalCompletionCode_descendant_law rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable]

/-- The exact prefix/product law holds jointly for actual completed spaces and
the original vertex-labelled metric code. Thus conditioning does not discard
terminal or persistent-vertex information. -/
theorem markedChemicalCompletionCode_prefix_frontier_law
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => ((fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        marks coordinate.val), fun group => markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family
          (innovationTreeShift rule (addresses group) marks))) =
    (Measure.infinitePi (fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.val.2 0)).prod
    (Measure.infinitePi (fun _ : Group => (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family))) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have jointLaw := (markedChemicalCompletionCode_prefix_frontier_independent rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable
    addresses distinct depth sameLength).map_prod_eq_prod_map_map
      (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)).aemeasurable
      (measurable_pi_lambda _ (fun group =>
        (markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable).comp
          (innovationTreeShift_measurable rule (addresses group)))).aemeasurable
  simp only [Function.comp_def] at jointLaw
  rw [jointLaw,
    markedChemicalCompletionCode_frontier_law rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable
      addresses distinct depth sameLength]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective
end
end IGSIII.Geometry

