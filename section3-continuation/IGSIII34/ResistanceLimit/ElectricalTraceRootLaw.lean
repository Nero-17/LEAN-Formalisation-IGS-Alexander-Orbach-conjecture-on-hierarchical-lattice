import IGSIII.Probability.IndependentPrefix
import IGSIII34.Percolation.ElectricalStationaryField
import IGSIII34.Forms.BlockZeroEnergyScaling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory ProbabilityTheory

/-- All original C/N labels and every labelled finite resistance determine
the full resistance form through its finite trace minima. Both noncrossing
sides remain in the same random code. -/
def ElectricalTraceCode (rule : Rule) :=
  ((List (Fin rule.edges) × Bool) → Configuration rule.edges) ×
    (∀ depth, Fin (rule.generation depth).edges → ℝ)

instance electricalTraceRootLawCodeMeasurableSpace (rule : Rule) : MeasurableSpace (ElectricalTraceCode rule) :=
  inferInstanceAs (MeasurableSpace (((List (Fin rule.edges) × Bool) → Configuration rule.edges) ×
    (∀ depth, Fin (rule.generation depth).edges → ℝ)))

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

def electricalTraceCode (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ElectricalTraceCode rule :=
  (marks, fun depth edge => stationaryGenerationResistance rule
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks) growth depth [] edge)

theorem electricalTraceCode_measurable : Measurable (electricalTraceCode rule p positive belowOne fixedPoint growth value) := by
  apply measurable_id.prodMk
  apply measurable_pi_lambda
  intro depth
  apply measurable_pi_lambda
  intro edge
  exact measurable_const.mul (electricalField_measurable rule p positive belowOne fixedPoint value _)

theorem electricalTraceCode_descendant_law (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => electricalTraceCode rule p positive belowOne fixedPoint growth value (innovationTreeShift rule address marks)) =
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (electricalTraceCode rule p positive belowOne fixedPoint growth value) := by
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map
    (electricalTraceCode rule p positive belowOne fixedPoint growth value ∘ innovationTreeShift rule address) = _
  rw [← Measure.map_map (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value)
    (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq]

theorem electricalTraceCode_prefix_frontier_independent
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) => marks coordinate.val)
      (fun marks group => electricalTraceCode rule p positive belowOne fixedPoint growth value
        (innovationTreeShift rule (addresses group) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (innovationPrefix_frontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    measurable_id (measurable_pi_lambda _ (fun group =>
      (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value).comp (measurable_pi_apply group)))

theorem electricalTraceCode_frontier_law
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks group => electricalTraceCode rule p positive belowOne fixedPoint growth value
        (innovationTreeShift rule (addresses group) marks)) =
    Measure.infinitePi (fun _ : Group => (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (electricalTraceCode rule p positive belowOne fixedPoint growth value)) := by
  have independent := (innovationFrontier_independent rule p positive belowOne fixedPoint addresses distinct depth sameLength).comp
    (fun _ => electricalTraceCode rule p positive belowOne fixedPoint growth value)
    (fun _ => electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value)
  have law := iIndepFun.map_fun_eq_infinitePi_map (fun group =>
    (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value).comp
      (innovationTreeShift_measurable rule (addresses group))) independent
  simp only [Function.comp_def] at law
  rw [law]
  simp_rw [electricalTraceCode_descendant_law]

/-- The actual complete finite trace code is independent of the selecting
prefix. This product identity includes conditioning on connected sockets;
it does not assert independence between the two sides of one B socket. -/
theorem electricalTraceCode_prefix_frontier_law
    {Group : Type} (addresses : Group → List (Fin rule.edges)) (distinct : Function.Injective addresses)
    (depth : ℕ) (sameLength : ∀ group, (addresses group).length = depth) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => ((fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
        marks coordinate.val), fun group => electricalTraceCode rule p positive belowOne fixedPoint growth value
          (innovationTreeShift rule (addresses group) marks))) =
    (Measure.infinitePi (fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} =>
      Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.val.2 0)).prod
    (Measure.infinitePi (fun _ : Group => (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (electricalTraceCode rule p positive belowOne fixedPoint growth value))) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have law := (electricalTraceCode_prefix_frontier_independent rule p positive belowOne fixedPoint growth value
    addresses distinct depth sameLength).map_prod_eq_prod_map_map
      (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)).aemeasurable
      (measurable_pi_lambda _ (fun group =>
        (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value).comp
          (innovationTreeShift_measurable rule (addresses group)))).aemeasurable
  simp only [Function.comp_def] at law
  rw [law, electricalTraceCode_frontier_law rule p positive belowOne fixedPoint growth value addresses distinct depth sameLength]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective

theorem electricalTraceCode_shift_resistance
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (depth : ℕ) (edge : Fin (rule.generation depth).edges) :
    (electricalTraceCode rule p positive belowOne fixedPoint growth value (innovationTreeShift rule address marks)).2 depth edge =
      stationaryGenerationResistance rule
        (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks) growth depth address edge := by
  simp only [electricalTraceCode, stationaryGenerationResistance, electricalField,
    innovationTreeShift_append, List.nil_append]

end
end IGSIII34.ResistanceLimit
