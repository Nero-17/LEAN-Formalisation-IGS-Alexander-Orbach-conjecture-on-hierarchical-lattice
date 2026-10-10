import IGSIII34.Probability.ConditionalLp2
import IGSIII34.Percolation.ElectricalOmegaComparison
import IGSIII34.Percolation.ElectricalPrefix
import IGSIII34.Probability.PrefixMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem markedObservableLp_prefix_aestronglyMeasurable
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    AEStronglyMeasurable[coordinatePrefixFiltration
      (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)]
      (markedObservableLp rule p positive belowOne fixedPoint depth [] opened response)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have historyMeasurable := comap_measurable
    (m := (inferInstance : MeasurableSpace
      ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges)))
    (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
      (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}) => marks coordinate.val)
  have responseMeasurable := ((measurable_of_countable response).comp
    ((markedGenerationConfiguration_measurable rule depth [] opened).comp
      (innovationPrefixFill_measurable rule (depth+1)))).comp historyMeasurable
  rw [← coordinatePrefixFiltration_eq_comap] at responseMeasurable
  have measurable : Measurable[coordinatePrefixFiltration
      (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)]
      (fun marks => response (markedGenerationConfiguration rule marks depth [] opened)) := by
    simpa only [Function.comp_def, markedGenerationConfiguration_prefix_factor] using responseMeasurable
  exact measurable.stronglyMeasurable.aestronglyMeasurable.congr
    (markedObservableLp_ae rule p positive belowOne fixedPoint depth [] opened response).symm

theorem electricalOrbit_prefix_residual_le
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (coarse fine : ℕ) {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, IGSIII34.Probability.finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inverseMomentBound : IGSIII34.Probability.finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation fine).network p configuration)⁻¹^power) ≤ inverseMoment) :
    ‖electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2)-
      conditionalLp2 (independentInnovationLaw rule p positive belowOne fixedPoint)
        (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (coarse+1))
        ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (coarse+1))
        (electricalOrbitLp rule p positive belowOne fixedPoint growth (coarse+fine+2))‖ ≤
      2*(constant⁻¹*Real.sqrt ((2*secondMoment*Real.sqrt secondMoment*inverseMoment^(1/power))*
        (((rule.edges : ℝ)^(1/power))/deriv rule.network.reliability p)^(coarse+1))) := by
  apply (conditionalLp2_residual_le_approximation
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (coarse+1))
    ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (coarse+1))
    _ (markedObservableLp rule p positive belowOne fixedPoint coarse [] true
      (generationElectricalBlockMean rule p growth coarse fine))
    (markedObservableLp_prefix_aestronglyMeasurable rule p positive belowOne fixedPoint coarse true _)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [show coarse+fine+2 = (coarse+fine+1)+1 by omega,
    electricalOrbitLp_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le]
  exact marked_growth_electrical_residual_geometric rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds [] coarse fine powerAtLeastTwo
    secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative secondMomentBound inverseMomentBound

end
end IGSIII34.Percolation

