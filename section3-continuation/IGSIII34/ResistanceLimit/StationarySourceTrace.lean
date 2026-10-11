import IGSIII34.ResistanceLimit.SourceActualTrace
import IGSIII34.Percolation.ElectricalStationaryField

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

theorem actual_stationary_substitution_source_energy_le
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
      ∀ potential : Fin (Fintype.card (outer.SubstitutionVertex rule.network)) → ℝ,
        sourceComponentEnergy (network outer coarse)
          (fun edge => scalar * growth * electricalField rule p positive belowOne fixedPoint value
            (addresses edge.val) marks)
          (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex rule.network))) ≤
        sourceComponentEnergy (network (outer.substitute rule.network)
          (substitutionConfigurationEquiv (fun edge => marks (addresses edge, coarse edge))))
          (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
            (addresses ((substitutionOpenEdgeEquiv (fun edge => marks (addresses edge, coarse edge))).symm edge).1 ++
              [((substitutionOpenEdgeEquiv (fun edge => marks (addresses edge, coarse edge))).symm edge).2.val]) marks) potential := by
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
    have retained : coarse edge.val = true := (congrFun coarsens edge.val).symm.trans edge.property
    change electricalCell rule.network (marks (addresses edge.val, coarse edge.val))
      (fun child => scalar * electricalField rule p positive belowOne fixedPoint value
        (addresses edge.val ++ [child]) marks) = _
    rw [retained, electricalCell_scale rule.network _ (fun child => (fieldPositive _).le) scalarPositive.le,
      stationary (addresses edge.val)]
    ring
  intro potential
  have bound := sourceComponentEnergy_le_actual_substitution_energy outer rule.network
    (fun edge => marks (addresses edge, coarse edge))
    (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
      (addresses edge.1 ++ [edge.2.val]) marks)
    (fun edge => mul_pos scalarPositive (fieldPositive _)) potential
  rw [coarseResistances] at bound
  exact (congrArg (fun configuration : Configuration outerEdges =>
    sourceComponentEnergy (network outer configuration)
      (fun edge => scalar * growth * electricalField rule p positive belowOne fixedPoint value
        (addresses edge.val) marks)
      (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex rule.network))))
    coarsens).symm.le.trans bound

end
end IGSIII34.ResistanceLimit
