import IGSIII34.Probability.PositiveResampling
import IGSIII34.Resistance.ResamplingCurrent

set_option autoImplicit false
namespace IGSIII34.Probability
noncomputable section
open scoped BigOperators
variable {Outcome : Type*} [Fintype Outcome]

theorem finiteMean_mono (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    {first second : Outcome → ℝ} (comparison : ∀ outcome, first outcome ≤ second outcome) :
    finiteMean weight first ≤ finiteMean weight second :=
  Finset.sum_le_sum (fun outcome _ => mul_le_mul_of_nonneg_left (comparison outcome) (nonnegative outcome))

theorem finiteMean_mul_const (weight response : Outcome → ℝ) (scalar : ℝ) :
    finiteMean weight (fun outcome => response outcome * scalar) = finiteMean weight response * scalar := by
  simp only [finiteMean, ← mul_assoc, Finset.sum_mul]

theorem finiteMean_const_mul (weight response : Outcome → ℝ) (scalar : ℝ) :
    finiteMean weight (fun outcome => scalar * response outcome) = scalar * finiteMean weight response := by
  simp only [finiteMean, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end
end IGSIII34.Probability

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open IGSIII34.Probability
open scoped BigOperators
variable {Vertex State : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype State]
  {count : ℕ}

theorem finite_electrical_variance_bound (network : FiniteNetwork Vertex (Fin count))
    (connected : network.graph.Reachable network.source network.target)
    (weight : State → ℝ) (nonnegative : ∀ value, 0 ≤ weight value)
    (normalized : ∑ value, weight value = 1)
    (resistance : State → ℝ) (positive : ∀ value, 0 < resistance value) :
    finiteVariance (tupleWeight (fun _ : Fin count => weight))
      (fun input : Fin count → State => network.effectiveResistance (fun edge => resistance (input edge))) ≤
      2 * finiteMean weight (fun value => resistance value ^ 2) *
        finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → State =>
          ∑ edge, network.minimizingCurrent connected (fun edge => resistance (input edge))
            (fun edge => positive (input edge)) edge ^ 4) := by
  apply (finite_product_variance_le_positive_resampling count (fun _ => weight)
    (fun _ => nonnegative) (fun _ => normalized) _).trans
  have energyBound : positiveResamplingEnergy (fun _ : Fin count => weight)
      (fun input : Fin count → State => network.effectiveResistance (fun edge => resistance (input edge))) ≤
        finiteMean weight (fun value => resistance value ^ 2) *
          finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → State =>
            ∑ edge, network.minimizingCurrent connected (fun edge => resistance (input edge))
              (fun edge => positive (input edge)) edge ^ 4) := by
    unfold positiveResamplingEnergy
    calc
      _ ≤ finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → State =>
          ∑ edge, finiteMean weight (fun value => resistance value ^ 2) *
            network.minimizingCurrent connected (fun edge => resistance (input edge))
              (fun edge => positive (input edge)) edge ^ 4) := by
        apply finiteMean_mono _ (tupleWeight_nonnegative _ (fun _ => nonnegative))
        intro input
        apply Finset.sum_le_sum
        intro edge _
        rw [← finiteMean_mul_const]
        apply finiteMean_mono _ nonnegative
        intro replacement
        have updatedInput :
            (fun index => resistance (Function.update input edge replacement index)) =
            Function.update (fun index => resistance (input index)) edge (resistance replacement) := by
          funext index
          by_cases same : index = edge <;> simp [same]
        dsimp only
        rw [updatedInput]
        exact network.resistance_resampling_positivePart_sq_le connected
          (fun index => resistance (input index)) (fun index => positive (input index))
          edge (resistance replacement) (positive replacement).le
      _ = _ := by
        simp only [← Finset.mul_sum]
        exact finiteMean_const_mul _ _ _
  calc
    _ ≤ 2 * (finiteMean weight (fun value => resistance value ^ 2) *
        finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → State =>
          ∑ edge, network.minimizingCurrent connected (fun edge => resistance (input edge))
            (fun edge => positive (input edge)) edge ^ 4)) := mul_le_mul_of_nonneg_left energyBound (by norm_num)
    _ = _ := by ring

end
end IGSIII34.Resistance.FiniteNetwork
