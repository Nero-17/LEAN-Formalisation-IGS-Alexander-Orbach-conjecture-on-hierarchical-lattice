import IGSIII34.Diffusion.ElectricalEdgeBoundaryProjectionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology ENNReal

local instance electricalDegreeConvergenceMeasurableCompletion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance electricalDegreeConvergenceBorelCompletion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

/-- The actual degree speed measures, placed at their original electrical
birth vertices, converge to the boundary Perron measure. Finite component
ownership and original electrical mesh bounds prove the entire sequence. -/
theorem actualElectrical_degree_mass_tendsto_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (weight : List (Fin rule.edges × Bool) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (limits : ∀ age word, Tendsto (fun fine => edgeComponentWordWeight rule marks.val fine age word) atTop
      (𝓝 (weight (List.ofFn word))))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)
    (projection : Tendsto (fun depth => levyProkhorovEDist
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0)) :
    Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive depth) (boundary.map realization)) atTop (𝓝 0) := by
  classical
  obtain ⟨edge⟩ := clusterEdge_nonempty rule.network (marks.val ([], true)) (marks.property.2.1 [] true)
  let fallback : ∀ age, Fin (age + 1) → (Fin rule.edges × Bool) := fun _ _ => (edge.val, true)
  let anchor := fun age => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age
  let fineError := fun age fine => levyProkhorovEDist
    ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map (anchor age))
    (boundary.map (fun path => anchor age (path (age + 1))))
  let coarseError := fun age => levyProkhorovEDist (boundary.map (fun path => anchor age (path (age + 1)))) (boundary.map realization)
  let mesh := fun age => ENNReal.ofReal (coefficient * eta ^ (age + 1)) + coarseError age
  have realMesh : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)).const_mul coefficient
  have ennrealMesh : Tendsto (fun age : ℕ => ENNReal.ofReal (coefficient * eta ^ (age + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp realMesh
  have meshConvergence : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh, coarseError, anchor, zero_add] using ennrealMesh.add projection
  have errorConvergence : ∀ age, Tendsto (fineError age) atTop (𝓝 0) := fun age =>
    actual_edge_boundary_projection_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      weight nonnegative boundary atoms limits age
  apply tendsto_zero_of_shifted_comparison _ mesh fineError start meshConvergence errorConvergence
  intro age beyond fine
  have degreeProjection := actualElectrical_degree_projection_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive fieldLimit eta coefficient start etaNonnegative coefficientNonnegative radiusBound fine age beyond (fallback age)
  have triangle := (levyProkhorovEDist_triangle
    (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive (fine + (age + 1)))
    ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map (anchor age)) (boundary.map realization)).trans
    (add_le_add degreeProjection (levyProkhorovEDist_triangle
      ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map (anchor age))
      (boundary.map (fun path => anchor age (path (age + 1)))) (boundary.map realization)))
  apply triangle.trans
  change ENNReal.ofReal (coefficient * eta ^ (age + 1)) + (fineError age fine + coarseError age) ≤ mesh age + mesh age + fineError age fine
  calc
    _ = mesh age + fineError age fine := by dsimp only [mesh]; ac_rfl
    _ ≤ mesh age + mesh age + fineError age fine := add_le_add (le_self_add : mesh age ≤ mesh age + mesh age) le_rfl

end
end IGSIII34.Diffusion



