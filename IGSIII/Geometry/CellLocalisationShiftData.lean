import IGSIII.Geometry.CellLocalisationAddressScaling

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory Filter
open scoped Topology ENNReal

theorem innovationTreeShift_crossing (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (address : List (Fin rule.edges)) :
    ∀ suffix opened, rule.network.crosses (innovationTreeShift rule address marks (suffix, opened)) = opened :=
  fun suffix opened => crossing (address ++ suffix) opened

theorem innovationTreeShift_coherent (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coherent : ∀ address opened, configurationSequenceCoherent rule
      (fun depth => markedGenerationConfiguration rule marks depth address opened))
    (address : List (Fin rule.edges)) :
    ∀ suffix opened, configurationSequenceCoherent rule
      (fun depth => markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth suffix opened) := by
  intro suffix opened depth
  change rule.coarsenGeneration depth (markedGenerationConfiguration rule (innovationTreeShift rule address marks) (depth + 1) suffix opened) =
    markedGenerationConfiguration rule (innovationTreeShift rule address marks) depth suffix opened
  rw [markedGenerationConfiguration_shift, markedGenerationConfiguration_shift]
  exact coherent (address ++ suffix) opened depth

theorem innovationTreeShift_field_positive (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fieldPositive : ∀ suffix, 0 < chemicalField rule p positive belowOne fixedPoint value suffix marks)
    (address : List (Fin rule.edges)) :
    ∀ suffix, 0 < chemicalField rule p positive belowOne fixedPoint value suffix (innovationTreeShift rule address marks) := by
  intro suffix
  rw [chemicalField_shift]
  exact fieldPositive (address ++ suffix)

theorem innovationTreeShift_field_convergence (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth amplitude : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fieldConvergence : ∀ suffix, Tendsto
      (fun depth => (markedTerminalDistance rule marks depth suffix true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value suffix marks)))
    (address : List (Fin rule.edges)) :
    ∀ suffix, Tendsto
      (fun depth => (markedTerminalDistance rule (innovationTreeShift rule address marks) depth suffix true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value suffix (innovationTreeShift rule address marks))) := by
  intro suffix
  have distanceIdentity : (fun depth => (markedTerminalDistance rule (innovationTreeShift rule address marks) depth suffix true : ℝ) / growth ^ (depth + 1)) =
      (fun depth => (markedTerminalDistance rule marks depth (address ++ suffix) true : ℝ) / growth ^ (depth + 1)) := by
    funext depth
    unfold markedTerminalDistance
    rw [markedGenerationConfiguration_shift]
  rw [distanceIdentity, chemicalField_shift]
  exact fieldConvergence (address ++ suffix)

end
end IGSIII.Geometry

