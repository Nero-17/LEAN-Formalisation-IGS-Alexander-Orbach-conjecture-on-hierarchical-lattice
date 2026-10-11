import IGSIII34.ResistanceLimit.ElectricalTraceRootLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory ProbabilityTheory

theorem finite_source_energy_measurable_resistance
    {vertices edges : ℕ} (finiteNetwork : Universality.FiniteNetwork vertices edges) (sourceSide : Bool)
    (potential : Fin vertices → ℝ) :
    Measurable (fun pair : Configuration edges × (Fin edges → ℝ) =>
      sourceComponentEnergy (sideNetwork (network finiteNetwork pair.1) sourceSide)
        (fun edge => pair.2 edge.val) potential) := by
  classical
  apply measurable_from_prod_countable_right
  intro configuration
  change Measurable (fun resistance : Fin edges → ℝ =>
    sourceComponentEnergy (sideNetwork (network finiteNetwork configuration) sourceSide)
      (fun edge => resistance edge.val) potential)
  unfold sourceComponentEnergy finiteEnergy
  apply Finset.measurable_sum
  intro edge _
  by_cases retained : (sideNetwork (network finiteNetwork configuration) sourceSide).graph.Reachable
      (sideNetwork (network finiteNetwork configuration) sourceSide).source
      ((sideNetwork (network finiteNetwork configuration) sourceSide).endpoint edge).1
  · simp only [if_pos retained]
    exact (measurable_pi_apply edge.val).inv.mul measurable_const
  · simp only [if_neg retained]
    exact measurable_const

def electricalTraceCodeEnergy (rule : Rule) (code : ElectricalTraceCode rule)
    (opened sourceSide : Bool) (depth : ℕ) (potential : Fin (rule.generation depth).vertices → ℝ) : ℝ :=
  sourceComponentEnergy (sideNetwork (network (rule.generation depth).network
    (markedGenerationConfiguration rule code.1 depth [] opened)) sourceSide)
    (fun edge => code.2 depth edge.val) potential

theorem electricalTraceCodeEnergy_measurable (rule : Rule) (opened sourceSide : Bool)
    (depth : ℕ) (potential : Fin (rule.generation depth).vertices → ℝ) :
    Measurable (fun code => electricalTraceCodeEnergy rule code opened sourceSide depth potential) := by
  exact (finite_source_energy_measurable_resistance (rule.generation depth).network sourceSide potential).comp
    (((markedGenerationConfiguration_measurable rule depth [] opened).comp measurable_fst).prodMk
      ((measurable_pi_apply depth).comp measurable_snd))

def electricalTraceCodeLimitingEnergy (rule : Rule) (code : ElectricalTraceCode rule)
    (opened sourceSide : Bool) (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) : ℝ :=
  ⨆ depth, electricalTraceCodeEnergy rule code opened sourceSide depth (potentials depth)

theorem electricalTraceCodeLimitingEnergy_measurable (rule : Rule) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    Measurable (fun code => electricalTraceCodeLimitingEnergy rule code opened sourceSide potentials) :=
  Measurable.iSup (fun depth => electricalTraceCodeEnergy_measurable rule opened sourceSide depth (potentials depth))

theorem electricalTraceCode_finite_energy_measurableSet (rule : Rule) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    MeasurableSet {code : ElectricalTraceCode rule | BddAbove (Set.range
      (fun depth => electricalTraceCodeEnergy rule code opened sourceSide depth (potentials depth)))} :=
  measurableSet_bddAbove_range (fun depth => electricalTraceCodeEnergy_measurable rule opened sourceSide depth (potentials depth))

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

/-- Monotone completion does not change the actual descendant marginal law:
the limiting energy itself is a measurable functional of the finite traces. -/
theorem electrical_limiting_energy_descendant_law
    (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value (innovationTreeShift rule address marks))
        opened sourceSide potentials) =
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) := by
  have measurable : Measurable (fun marks => electricalTraceCodeLimitingEnergy rule
      (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) :=
    (electricalTraceCodeLimitingEnergy_measurable rule opened sourceSide potentials).comp
    (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value)
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map
    ((fun marks => electricalTraceCodeLimitingEnergy rule
      (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) ∘
      innovationTreeShift rule address) = _
  rw [← Measure.map_map measurable (innovationTreeShift_measurable rule address),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq]

end
end IGSIII34.ResistanceLimit
