import IGSIII34.Percolation.ConnectedResistance
import IGSIII34.Resistance.Jensen
import IGSIII.Chemical.GeodesicProductEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators

theorem finite_iid_electricalCell_mean_sandwich
    {vertices edges : ℕ} {State : Type*} [Fintype State]
    (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : network.crosses configuration = true)
    (weight : State → ℝ) (nonnegative : ∀ state, 0 ≤ weight state)
    (normalized : ∑ state, weight state = 1)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state)
    (meanOne : finiteMean weight resistance = 1)
    (constant : ℝ)
    (inverseBound : finiteMean weight (fun state => (resistance state)⁻¹) ≤ constant) :
    unitConfigurationResistance network configuration / constant ≤
        finiteMean (tupleWeight (fun _ : Fin edges => weight))
          (fun sample => electricalCell network configuration (fun edge => resistance (sample edge))) ∧
      finiteMean (tupleWeight (fun _ : Fin edges => weight))
          (fun sample => electricalCell network configuration (fun edge => resistance (sample edge))) ≤
        unitConfigurationResistance network configuration := by
  have inverseAtLeastOne : 1 ≤ finiteMean weight (fun state => (resistance state)⁻¹) := by
    have bound := Resistance.FiniteNetwork.weighted_mean_mul_reciprocal_mean_ge_one
      weight resistance nonnegative normalized positive
    change 1 ≤ finiteMean weight resistance * finiteMean weight (fun state => (resistance state)⁻¹) at bound
    simpa only [meanOne, one_mul] using bound
  have inversePositive := zero_lt_one.trans_le inverseAtLeastOne
  have connected := connected_of_crosses network configuration crosses
  have cellBounds := (IGSIII34.Percolation.network network configuration).finite_random_resistance_mean_sandwich
    connected (tupleWeight (fun _ : Fin edges => weight))
    (tupleWeight_nonnegative _ (fun _ => nonnegative)) (tupleWeight_normalized _ (fun _ => normalized))
    (fun sample edge => resistance (sample edge.val)) (fun sample edge => positive (sample edge.val))
    (fun edge => by
      change finiteMean (tupleWeight (fun _ : Fin edges => weight))
        (fun sample => resistance (sample edge.val)) = 1
      exact (IGSIII.Chemical.finiteMean_tuple_local (fun _ : Fin edges => weight)
        (fun _ => normalized) edge.val resistance).trans meanOne)
    inversePositive
    (fun edge => by
      change finiteMean (tupleWeight (fun _ : Fin edges => weight))
        (fun sample => (resistance (sample edge.val))⁻¹) = finiteMean weight (fun state => (resistance state)⁻¹)
      exact IGSIII.Chemical.finiteMean_tuple_local (fun _ : Fin edges => weight)
        (fun _ => normalized) edge.val (fun state => (resistance state)⁻¹))
  refine ⟨?_, cellBounds.2⟩
  apply le_trans _ cellBounds.1
  apply div_le_div_of_nonneg_left
    ((IGSIII34.Percolation.network network configuration).effectiveResistance_pos_of_connected connected
      (fun _ => zero_lt_one)).le inversePositive inverseBound

end
end IGSIII34.Percolation
