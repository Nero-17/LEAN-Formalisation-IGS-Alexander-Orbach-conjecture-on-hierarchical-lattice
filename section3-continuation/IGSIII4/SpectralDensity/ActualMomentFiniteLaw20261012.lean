import IGSIII4.SpectralDensity.ActualMomentIndexedResponse20261012
import IGSIII34.Percolation.ElectricalTree
import IGSIII34.Probability.FiniteTensorization
import IGSIII34.Probability.FiniteProduct

set_option autoImplicit false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open IGSIII34.Probability IGSIII34.Percolation
variable {Outcome : Type*} [Fintype Outcome]

theorem electricalCell_eq_circuitVoltage20261012 (blocks paths interior : ℕ)
    (configuration : Fin (Fintype.card (Edge blocks paths interior)) → Bool)
    (input : Fin (Fintype.card (Edge blocks paths interior)) → ℝ)
    (positive : ∀ edge, 0 < input edge)
    (crosses : (network blocks paths interior).crosses configuration = true) :
    electricalCell (network blocks paths interior) configuration input =
      circuitVoltage (fun edge => configuration (Fintype.equivFin _ edge))
        (fun edge => input (Fintype.equivFin _ edge)) := by
  have identity := actual_indexed_circuit_resistance20261012
    (fun edge : Edge blocks paths interior => configuration (Fintype.equivFin _ edge))
    (fun edge => input (Fintype.equivFin _ edge)) (fun edge => positive _)
    ((network_crosses_iff_circuit configuration).mp crosses)
  have configurationIdentity : (fun edge => configuration
      (Fintype.equivFin (Edge blocks paths interior)
        ((Fintype.equivFin (Edge blocks paths interior)).symm edge))) = configuration := by
    funext edge
    simp only [Equiv.apply_symm_apply]
  change electricalCell (network blocks paths interior)
    (fun edge => configuration (Fintype.equivFin (Edge blocks paths interior)
      ((Fintype.equivFin (Edge blocks paths interior)).symm edge)))
    (fun edge => input (Fintype.equivFin (Edge blocks paths interior)
      ((Fintype.equivFin (Edge blocks paths interior)).symm edge))) = _ at identity
  simpa only [configurationIdentity, Equiv.apply_symm_apply] using identity

def weightedCellObservable (blocks paths interior : ℕ) (parameter : ℝ)
    (weight response : Outcome → ℝ) (observable : ℝ → ℝ) : ℝ :=
  finiteMean ((network blocks paths interior).conditionalCellWeight parameter true)
    (fun configuration => finiteMean (productWeight weight) (fun input =>
      observable (electricalCell (network blocks paths interior) configuration
        (fun edge => response (input edge)))))

def weightedCellMean (blocks paths interior : ℕ) (parameter : ℝ)
    (weight response : Outcome → ℝ) : ℝ :=
  weightedCellObservable blocks paths interior parameter weight response id

def weightedCellSecondMoment (blocks paths interior : ℕ) (parameter : ℝ)
    (weight response : Outcome → ℝ) : ℝ :=
  weightedCellObservable blocks paths interior parameter weight response (fun value => value ^ 2)

end
end IGSIII4.SpectralDensity.ActualFamily
