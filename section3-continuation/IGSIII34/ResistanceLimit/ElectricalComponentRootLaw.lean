import IGSIII34.ResistanceLimit.ElectricalEnergyRootLaw
import Mathlib.Data.Real.Pointwise

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII.Geometry MeasureTheory ProbabilityTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

theorem electricalTraceCodeEnergy_shift
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool) (depth : ℕ)
    (potential : Fin (rule.generation depth).vertices → ℝ) :
    electricalTraceCodeEnergy rule
      (electricalTraceCode rule p positive belowOne fixedPoint growth value (innovationTreeShift rule address marks))
      opened sourceSide depth potential =
    sourceComponentEnergy (sideNetwork (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth address opened)) sourceSide)
      (fun edge => stationaryGenerationResistance rule
        (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
        growth depth address edge.val) potential := by
  have configurationIdentity : markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth [] opened =
      markedGenerationConfiguration rule marks depth address opened := by
    simpa only [List.append_nil] using
      IGSIII.Chemical.Substitution.markedGenerationConfiguration_shift rule marks address [] opened depth
  simp only [electricalTraceCodeEnergy, electricalTraceCode]
  erw [configurationIdentity]
  congr 1
  funext edge
  simp only [stationaryGenerationResistance, electricalField, innovationTreeShift_append, List.nil_append]

def electricalComponentGlobalEnergy
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) : ℝ :=
  ⨆ depth, sourceComponentEnergy (sideNetwork (network (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth (generationEdgeAddress rule coarse chosen) opened)) sourceSide)
    (fun edge => stationaryGenerationResistance rule
      (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
      growth (coarse + depth + 1) [] ((generationBlockCellEmbedding rule coarse depth chosen).edge edge.val))
    (potentials depth)

/-- This is the actual component contribution in global normalization,
including its complete finite-energy trace limit. -/
theorem electrical_component_global_energy_scaling
    (growthPositive : 0 < growth)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    electricalComponentGlobalEnergy rule p positive belowOne fixedPoint growth value marks coarse chosen opened sourceSide potentials =
      growth ^ (coarse + 1) * electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value
          (innovationTreeShift rule (generationEdgeAddress rule coarse chosen) marks)) opened sourceSide potentials := by
  unfold electricalComponentGlobalEnergy electricalTraceCodeLimitingEnergy
  simp_rw [stationary_block_side_energy_scaling, ← electricalTraceCodeEnergy_shift]
  exact (Real.mul_iSup_of_nonneg (pow_pos growthPositive _).le _).symm

/-- The energy root law is a pushforward equality on the original innovation
space, not just a samplewise scaling assertion. -/
theorem electrical_component_global_energy_root_law
    (growthPositive : 0 < growth) (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges)
    (opened sourceSide : Bool) (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => electricalComponentGlobalEnergy rule p positive belowOne fixedPoint growth value
        marks coarse chosen opened sourceSide potentials) =
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => growth ^ (coarse + 1) * electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) := by
  have measurable : Measurable (fun marks => growth ^ (coarse + 1) * electricalTraceCodeLimitingEnergy rule
      (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) :=
    measurable_const.mul ((electricalTraceCodeLimitingEnergy_measurable rule opened sourceSide potentials).comp
      (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value))
  simp_rw [electrical_component_global_energy_scaling rule p positive belowOne fixedPoint growth value growthPositive]
  change (independentInnovationLaw rule p positive belowOne fixedPoint).map
    ((fun marks => growth ^ (coarse + 1) * electricalTraceCodeLimitingEnergy rule
      (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials) ∘
      innovationTreeShift rule (generationEdgeAddress rule coarse chosen)) = _
  rw [← Measure.map_map measurable (innovationTreeShift_measurable rule _),
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint _).map_eq]

/-- Conditioning on the finite selecting prefix leaves the descendant root
energy law unchanged. The two B-side decoders use one common random code. -/
theorem electrical_limiting_energy_prefix_independent
    (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < address.length}) =>
        marks coordinate.val)
      (fun marks => electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value (innovationTreeShift rule address marks))
        opened sourceSide potentials)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have independent := electricalTraceCode_prefix_frontier_independent rule p positive belowOne fixedPoint growth value
    (fun _ : Unit => address) (fun first last _ => Subsingleton.elim first last)
    address.length (fun _ => rfl)
  exact independent.comp measurable_id
    ((electricalTraceCodeLimitingEnergy_measurable rule opened sourceSide potentials).comp (measurable_pi_apply ()))

end
end IGSIII34.ResistanceLimit
