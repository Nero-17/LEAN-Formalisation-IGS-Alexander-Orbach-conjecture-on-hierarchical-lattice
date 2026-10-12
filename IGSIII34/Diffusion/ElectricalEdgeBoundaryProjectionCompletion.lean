import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion
import IGSIII34.Diffusion.FiniteBoundaryProjectionCompletion
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
local instance electricalEdgeBoundaryMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance electricalEdgeBoundaryBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem actual_edge_boundary_projection_tendsto_completion
    (weight : List (Fin rule.edges × Bool) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (limits : ∀ age word, Tendsto (fun fine => edgeComponentWordWeight rule marks.val fine age word) atTop
      (𝓝 (weight (List.ofFn word)))) (age : ℕ) :
    Tendsto (fun fine => levyProkhorovEDist
      ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map
        (electricalDegreeWordAnchorCompletion rule p positive belowOne fixedPoint growth value growthPositive marks age))
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property age (path (age + 1))))) atTop (𝓝 0) := by
  let anchor : (Fin (age + 1) → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks :=
    electricalDegreeWordAnchorCompletion rule p positive belowOne fixedPoint growth value growthPositive marks age
  let marginal := boundary.map (fun path => path (age + 1))
  have marginalAtoms (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
      marginal {word} = ENNReal.ofReal (weight (List.ofFn word)) := by
    rw [Measure.map_apply (measurable_pi_apply (age + 1)) (measurableSet_singleton word)]
    exact atoms (age + 1) word
  have result := finite_boundary_projection_tendsto_completion
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)
    (fun fine => edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1))
    (fun fine word => edgeComponentWordWeight rule marks.val fine (age + 1) word)
    (fun fine word => edgeComponentWordWeight_nonnegative rule marks.val fine (age + 1) word)
    (fun fine => edgeComponentWordWeight_sum rule marks.val marks.property.2.1 fine (age + 1))
    (fun _ => rfl) (fun word => weight (List.ofFn word)) (fun word => nonnegative _)
    (probability_boundary_weights_sum weight nonnegative boundary atoms (age + 1))
    (limits (age + 1)) marginal marginalAtoms anchor
  have mapIdentity : marginal.map anchor = boundary.map (fun path => anchor (path (age + 1))) :=
    Measure.map_map (measurable_of_finite anchor) (measurable_pi_apply (age + 1))
  exact result.congr' (Eventually.of_forall fun fine => congrArg
    (fun measure => levyProkhorovEDist ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map anchor) measure) mapIdentity)

end
end IGSIII34.Diffusion