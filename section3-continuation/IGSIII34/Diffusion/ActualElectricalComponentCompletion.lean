import IGSIII34.Diffusion.RootedElectricalIntrinsicEnergy
import IGSIII34.ResistanceLimit.ActualStationaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

/-- The original actual compatibility event includes every component address
and both conditioning states; no limiting resistance is assumed. -/
def ComponentElectricalTypical
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : Prop :=
  (∀ address, 0 < electricalField rule p positive belowOne fixedPoint value address marks) ∧
  (∀ address opened, rule.network.crosses (marks (address, opened)) = opened) ∧
  ∀ depth address opened (first last : Fin (rule.generation depth).vertices),
    ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth address opened)).Reachable first last →
    pairResistance (network (rule.generation (depth + 1)).network (markedGenerationConfiguration rule marks (depth + 1) address opened))
      (fun edge => stationaryGenerationResistance rule
        (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
        growth (depth + 1) address edge.val)
      (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth address opened))
      (fun edge => stationaryGenerationResistance rule
        (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
        growth depth address edge.val) first last

theorem componentElectricalTypical_ae
    (growthPositive : 0 < growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks := by
  filter_upwards [electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    actual_stationary_generation_pair_compatible rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed]
    with marks fieldPositive crossing compatibility
  exact ⟨fieldPositive, crossing, compatibility⟩

variable (growthPositive : 0 < growth)
variable (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
variable (word : List (Fin rule.edges × Bool))

def actualElectricalComponentConfiguration (depth : ℕ) : Configuration (rule.generation depth).edges :=
  markedGenerationConfiguration rule marks.val depth (componentEdgeAddress word) (retainedComponentState rule marks.val word).massOpened

theorem actualElectricalComponentCoherent :
    configurationSequenceCoherent rule (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word) :=
  fun depth => markedGenerationConfiguration_coarsens rule marks.val marks.property.2.1 depth _ _

def actualElectricalComponentResistance (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth edge = true}) : ℝ :=
  stationaryGenerationResistance rule
    (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks.val)
    growth depth (componentEdgeAddress word) edge.val

include growthPositive in
theorem actualElectricalComponentResistance_positive :
    ∀ depth edge, 0 < actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word depth edge := by
  intro depth edge
  exact mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (marks.property.1 _)

theorem actualElectricalComponentResistance_compatible :
    ∀ depth (first last : Fin (rule.generation depth).vertices),
      ((rule.generation depth).network.openGraph (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth)).Reachable first last →
      pairResistance (network (rule.generation (depth + 1)).network (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word (depth + 1)))
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word (depth + 1))
        (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
      pairResistance (network (rule.generation depth).network (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth))
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word depth) first last :=
  fun depth first last reachable => marks.property.2.2 depth (componentEdgeAddress word)
    (retainedComponentState rule marks.val word).massOpened first last reachable

/-- The intrinsic resistance skeleton of the actual selected component,
using its original planted side, including an individual B side. -/
def ActualElectricalComponentSkeleton :=
  RootedElectricalSkeleton rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word)

instance actualElectricalComponentSkeletonMetricSpace :
    MetricSpace (ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word) := by
  unfold ActualElectricalComponentSkeleton
  infer_instance

def ActualElectricalComponentSpace := UniformSpace.Completion
  (ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word)

instance actualElectricalComponentSpaceMetricSpace :
    MetricSpace (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word) := by
  unfold ActualElectricalComponentSpace
  infer_instance

instance actualElectricalComponentSpaceCompleteSpace :
    CompleteSpace (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word) := by
  unfold ActualElectricalComponentSpace
  infer_instance

/-- The finite local energy on this carrier is exactly the selected-word
energy; inactive words are excluded precisely as in the retained-cell list. -/
theorem actualElectricalComponentIntrinsicTraceEnergy_eq_selected
    (live : retainedComponentState rule marks.val word ≠ .inactive) (depth : ℕ)
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ) :
    rootedElectricalIntrinsicTraceEnergy rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) depth potential =
    selectedComponentTraceEnergy rule marks.val depth word
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word depth)
      (fun vertex => potential (rootedElectricalSkeletonPoint rule
        (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
        (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
        (retainedComponentState rule marks.val word).sourceSelected
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
        (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
        (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) depth vertex)) := by
  rw [selectedComponentTraceEnergy, if_neg live]
  rfl


def actualElectricalComponentIntrinsicFiniteEnergy
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ) : Prop :=
  rootedElectricalIntrinsicFiniteEnergy rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) potential


def actualElectricalComponentIntrinsicEnergy
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ) : ℝ :=
  rootedElectricalIntrinsicEnergy rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) potential


def actualElectricalComponentIntrinsicExtension
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ) :
    C(ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word, ℝ) :=
  rootedElectricalIntrinsicCompletionExtension rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) potential


/-- The paper's intrinsic resistance inequality on each actual completed
retained component uses exactly its own local trace energy. -/
theorem actualElectricalComponent_completed_intrinsic_resistance_bound
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ)
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks word potential)
    (first last : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word) :
    (actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks word potential first -
      actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks word potential last) ^ 2 ≤
      dist first last * actualElectricalComponentIntrinsicEnergy rule p positive belowOne fixedPoint growth value growthPositive marks word potential := by
  exact rootedElectricalIntrinsicCompletionExtension_resistance_bound rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) potential finite first last

end
end IGSIII34.Diffusion
