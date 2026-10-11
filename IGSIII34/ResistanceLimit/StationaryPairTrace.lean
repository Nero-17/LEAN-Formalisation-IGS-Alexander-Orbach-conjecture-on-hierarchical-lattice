import IGSIII34.ResistanceLimit.PairTrace
import IGSIII34.Percolation.ElectricalStationaryField

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

/-- The actual stationary electrical weights give exact resistance isometries
on all old vertices of an arbitrary numbered substitution. -/
theorem actual_stationary_substitution_pair_trace
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    {outerVertices outerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (addresses : Fin outerEdges → List (Fin rule.edges)) (coarse : Configuration outerEdges)
    (scalar : ℝ) (scalarPositive : 0 < scalar) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ first last : Fin outerVertices, (outer.openGraph coarse).Reachable first last →
        pairResistance (network (outer.substitute rule.network)
            (substitutionConfigurationEquiv (fun edge => marks (addresses edge, coarse edge))))
          (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
            (addresses ((substitutionOpenEdgeEquiv (fun edge => marks (addresses edge, coarse edge))).symm edge).1 ++
              [((substitutionOpenEdgeEquiv (fun edge => marks (addresses edge, coarse edge))).symm edge).2.val]) marks)
          (Fintype.equivFin _ (Sum.inl first : outer.SubstitutionVertex rule.network))
          (Fintype.equivFin _ (Sum.inl last : outer.SubstitutionVertex rule.network)) =
          pairResistance (network outer coarse)
            (fun edge => scalar * growth * electricalField rule p positive belowOne fixedPoint value
              (addresses edge.val) marks) first last := by
  filter_upwards [electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks fieldPositive stationary crossing
  have coarsens : rule.network.coarseConfiguration (fun edge => marks (addresses edge, coarse edge)) = coarse := by
    funext edge
    exact crossing (addresses edge) (coarse edge)
  have coarseResistances : coarseResistance rule.network (fun edge => marks (addresses edge, coarse edge))
      (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
        (addresses edge.1 ++ [edge.2.val]) marks) =
      (fun edge => scalar * growth * electricalField rule p positive belowOne fixedPoint value (addresses edge.val) marks) := by
    funext edge
    have retained : coarse edge.val = true :=
      (congrFun coarsens edge.val).symm.trans edge.property
    change electricalCell rule.network (marks (addresses edge.val, coarse edge.val))
      (fun child => scalar * electricalField rule p positive belowOne fixedPoint value
        (addresses edge.val ++ [child]) marks) = _
    rw [retained, electricalCell_scale rule.network _ (fun child => (fieldPositive _).le) scalarPositive.le,
      stationary (addresses edge.val)]
    ring
  intro first last reachable
  have coarseReach : (outer.openGraph
      (rule.network.coarseConfiguration (fun edge => marks (addresses edge, coarse edge)))).Reachable first last := by
    rwa [coarsens]
  have trace := actual_substitution_pairResistance_trace outer rule.network
    (fun edge => marks (addresses edge, coarse edge))
    (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
      (addresses edge.1 ++ [edge.2.val]) marks)
    (fun edge => mul_pos scalarPositive (fieldPositive _)) first last coarseReach
  rw [coarseResistances] at trace
  exact trace.trans (congrArg (fun configuration : Configuration outerEdges =>
    pairResistance (network outer configuration)
      (fun edge => scalar * growth * electricalField rule p positive belowOne fixedPoint value
        (addresses edge.val) marks) first last) coarsens)

end
end IGSIII34.ResistanceLimit
