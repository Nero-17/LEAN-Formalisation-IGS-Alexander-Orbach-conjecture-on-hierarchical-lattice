import IGSIII34.ResistanceLimit.RetainedEnergy
import IGSIII34.Percolation.ElectricalStationaryField

/-!
# Exact finite traces of the actual stationary electrical field

The innovations, configurations and positive resistances are those of the
actual IGS model. Stationarity and the proved finite Dirichlet minimisation
identify the trace value, with no assumed trace-compatibility certificate.
For noncrossing cells both terminal components contribute zero to the coarse
trace; all microscopic interiors are still present in the minimisation.

The finite outer network is unrestricted, so all connected cells in dangling
coarse branches occur in the sum. Restriction to a source component and transport
to the persistent generation embeddings are separate later obligations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped BigOperators

theorem actual_stationary_substitution_trace
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
      ∀ boundary : Fin outerVertices → ℝ,
        sInf (skeletonPotentialEnergies outer rule.network
          (fun edge => marks (addresses edge, coarse edge))
          (fun edge => scalar * electricalField rule p positive belowOne fixedPoint value
            (addresses edge.1 ++ [edge.2.val]) marks) boundary) =
          ∑ edge, if coarse edge = true then
            (boundary (outer.endpoint edge).1 - boundary (outer.endpoint edge).2) ^ 2 /
              (scalar * growth * electricalField rule p positive belowOne fixedPoint value (addresses edge) marks)
            else 0 := by
  filter_upwards [electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks fieldPositive stationary crossing
  intro boundary
  rw [skeletonPotential_trace outer rule.network _ _
    (fun edge => mul_pos scalarPositive (fieldPositive _))]
  unfold coarsePotentialEnergy
  apply Finset.sum_congr rfl
  intro edge _
  unfold cellTraceEnergy
  rw [crossing (addresses edge) (coarse edge)]
  by_cases opened : coarse edge = true
  · simp only [opened, ↓reduceIte]
    change (boundary (outer.endpoint edge).1 - boundary (outer.endpoint edge).2) ^ 2 /
      electricalCell rule.network (marks (addresses edge, coarse edge))
        (fun child => scalar * electricalField rule p positive belowOne fixedPoint value
          (addresses edge ++ [child]) marks) = _
    rw [opened, electricalCell_scale rule.network _ (fun child => (fieldPositive _).le) scalarPositive.le,
      stationary (addresses edge)]
    congr 1
    ring
  · simp [opened]

end
end IGSIII34.ResistanceLimit
