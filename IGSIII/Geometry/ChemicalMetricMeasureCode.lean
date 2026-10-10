import IGSIII.Geometry.CellLocalisationMetricCode
import IGSIII.Mass.ComponentFinitePartition
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

private instance : MeasurableSpace OrientedState := ⊤
private instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

private theorem measurable_countable_dispatch {Sample Index Target : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Index] [MeasurableSpace Target]
    [Countable Index] [MeasurableSingletonClass Index]
    (functions : Index → Sample → Target) (functionsMeasurable : ∀ index, Measurable (functions index))
    (index : Sample → Index) (indexMeasurable : Measurable index) :
    Measurable (fun sample => functions (index sample) sample) :=
  (measurable_from_prod_countable_right (f := fun pair : Index × Sample => functions pair.1 pair.2) functionsMeasurable).comp (indexMeasurable.prodMk measurable_id)

theorem retainedComponentStateFrom_measurable (rule : Rule)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (address : List (Fin rule.edges × Bool)) :
    Measurable (fun marks => retainedComponentStateFrom rule marks ancestor parent address) := by
  induction address generalizing ancestor parent with
  | nil => exact measurable_const
  | cons choice tail inductionHypothesis =>
    have childMeasurable : Measurable (fun marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges => componentChildState
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) :=
      (measurable_of_countable (fun configuration : Configuration rule.edges => componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected configuration choice.1) choice.2)).comp (measurable_pi_apply (ancestor, parent.massOpened))
    exact measurable_countable_dispatch
      (fun child marks => retainedComponentStateFrom rule marks (ancestor ++ [choice.1]) child tail)
      (fun child => inductionHypothesis (ancestor ++ [choice.1]) child) _ childMeasurable

theorem markedOrientedVertexMass_measurable (rule : Rule)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    Measurable (fun marks => markedOrientedVertexMass rule marks depth address parent) :=
  (measurable_of_countable (fun configuration =>
    ((rule.generation depth).network.internalStateMass parent configuration : ℝ))).comp
      (markedGenerationConfiguration_measurable rule depth address parent.massOpened)

theorem markedComponentVertexMass_measurable (rule : Rule)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) :
    Measurable (fun marks => markedComponentVertexMass rule marks depth address) :=
  measurable_countable_dispatch
    (fun parent marks => markedOrientedVertexMass rule marks depth (componentEdgeAddress address) parent)
    (markedOrientedVertexMass_measurable rule depth (componentEdgeAddress address))
    (fun marks => retainedComponentState rule marks address)
    (retainedComponentStateFrom_measurable rule [] .connected address)

/-- A canonical measurable choice of the actual limiting cylinder mass. On the
proved probability-one set it is the counting limit, so no choice of a random
measure is used to establish its measurability. -/
def chemicalCylinderMassCode (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges × Bool)) : ℝ :=
  limsup (fun fine => markedComponentVertexMass rule marks fine address /
    markedComponentVertexMass rule marks (fine + address.length) []) atTop

theorem chemicalCylinderMassCode_measurable (rule : Rule) (address : List (Fin rule.edges × Bool)) :
    Measurable (fun marks => chemicalCylinderMassCode rule marks address) :=
  Measurable.limsup (fun fine => (markedComponentVertexMass_measurable rule fine address).div
    (markedComponentVertexMass_measurable rule (fine + address.length) []))

theorem chemicalCylinderMassCode_eq_limit (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges × Bool)) (weight : ℝ)
    (convergence : Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 weight)) :
    chemicalCylinderMassCode rule marks address = weight := convergence.limsup_eq

/-- The actual countable labelled metric-measure representation. Its first
coordinate includes the ordered planted graph labels and every finite pair
distance, and the second includes every limiting component-cylinder mass. -/
def ChemicalMetricMeasureCode (rule : Rule) :=
  ChemicalMetricCode rule × (List (Fin rule.edges × Bool) → ℝ)

instance chemicalMetricMeasureCodeMeasurableSpace (rule : Rule) : MeasurableSpace (ChemicalMetricMeasureCode rule) :=
  inferInstanceAs (MeasurableSpace (ChemicalMetricCode rule × (List (Fin rule.edges × Bool) → ℝ)))

def chemicalMetricMeasureCode (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ChemicalMetricMeasureCode rule :=
  ⟨chemicalMetricCode rule p positive belowOne fixedPoint growth amplitude value marks,
    chemicalCylinderMassCode rule marks⟩

theorem chemicalMetricMeasureCode_measurable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Measurable (chemicalMetricMeasureCode rule p positive belowOne fixedPoint growth amplitude value) :=
  (chemicalMetricCode_measurable rule p positive belowOne fixedPoint growth amplitude value).prodMk
    (measurable_pi_lambda _ (chemicalCylinderMassCode_measurable rule))

end
end IGSIII.Geometry


