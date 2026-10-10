import IGSIII34.Resistance.FiniteElectricalVariance
import IGSIII.Chemical.GeodesicProductEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open IGSIII34.Probability IGSIII.Chemical
open scoped BigOperators
attribute [local irreducible] effectiveResistance
variable {Vertex Edge Outcome : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

theorem finite_current_fourth_moment_le_inverse_envelope (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (resistance : Outcome → Edge → ℝ) (positive : ∀ outcome edge, 0 < resistance outcome edge)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) :
    finiteMean weight (fun outcome =>
      ∑ edge, network.minimizingCurrent connected (resistance outcome) (positive outcome) edge ^ 4) ≤
      (finiteMean weight (fun outcome => network.effectiveResistance (resistance outcome)^2)) ^ (1 / (2 : ℝ)) *
        (finiteMean weight (fun outcome => ∑ edge, (resistance outcome edge)⁻¹ ^ power)) ^ (1 / power) := by
  have powerPositive : 0 < power := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) powerAtLeastTwo
  have inverseNonnegative : 0 ≤ finiteMean weight (fun outcome => ∑ edge, (resistance outcome edge)⁻¹ ^ power) := by
    unfold finiteMean
    exact Finset.sum_nonneg (fun outcome _ => mul_nonneg (nonnegative outcome)
      (Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive outcome edge).le) _)))
  have envelopeBound := finiteMean_inverseEnvelope_sq_le weight resistance powerAtLeastTwo nonnegative normalized positive
  have firstFactorNonnegative : 0 ≤
      (finiteMean weight (fun outcome => network.effectiveResistance (resistance outcome)^2)) ^ (1 / (2 : ℝ)) := by
    apply Real.rpow_nonneg
    unfold finiteMean
    exact Finset.sum_nonneg (fun outcome _ => mul_nonneg (nonnegative outcome) (sq_nonneg _))
  calc
    _ ≤ finiteMean weight (fun outcome => network.effectiveResistance (resistance outcome) *
        inverseEnvelope (resistance outcome) power) := by
      apply finiteMean_mono weight nonnegative
      intro outcome
      exact (network.fourth_current_sum_le_resistance_inverse_bound connected (resistance outcome)
        (positive outcome) _ (inverse_le_inverseEnvelope _ powerPositive (positive outcome))).trans_eq (mul_comm _ _)
    _ ≤ (finiteMean weight (fun outcome => network.effectiveResistance (resistance outcome)^2)) ^ (1 / (2 : ℝ)) *
        (finiteMean weight (fun outcome => inverseEnvelope (resistance outcome) power^2)) ^ (1 / (2 : ℝ)) := by
      simpa only [IGSIII.Probability.finiteMean, finiteMean, Real.rpow_two] using
        IGSIII.Probability.finiteMean_mul_le_holder weight
          (fun outcome => network.effectiveResistance (resistance outcome))
          (fun outcome => inverseEnvelope (resistance outcome) power) Real.HolderConjugate.two_two
          nonnegative (fun outcome => (network.effectiveResistance_pos_of_connected connected (positive outcome)).le)
          (fun outcome => inverseEnvelope_nonnegative _ (positive outcome))
    _ ≤ (finiteMean weight (fun outcome => network.effectiveResistance (resistance outcome)^2)) ^ (1 / (2 : ℝ)) *
        ((finiteMean weight (fun outcome => ∑ edge, (resistance outcome edge)⁻¹ ^ power)) ^ (2 / power)) ^ (1 / (2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ firstFactorNonnegative
      apply Real.rpow_le_rpow _ _ (by norm_num)
      · unfold finiteMean
        exact Finset.sum_nonneg (fun outcome _ => mul_nonneg (nonnegative outcome) (sq_nonneg _))
      · exact envelopeBound
    _ = _ := by
      rw [← Real.rpow_mul inverseNonnegative]
      congr 2
      ring

theorem finite_iid_current_fourth_moment_bound {count : ℕ}
    (network : FiniteNetwork Vertex (Fin count))
    (connected : network.graph.Reachable network.source network.target)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (resistance : Outcome → ℝ) (positive : ∀ outcome, 0 < resistance outcome)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (inverseMoment : ℝ)
    (inverseBound : finiteMean weight (fun outcome => (resistance outcome)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → Outcome =>
      ∑ edge, network.minimizingCurrent connected (fun edge => resistance (input edge))
        (fun edge => positive (input edge)) edge ^ 4) ≤
      (finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → Outcome =>
        network.effectiveResistance (fun edge => resistance (input edge))^2)) ^ (1 / (2 : ℝ)) *
        ((count : ℝ) * inverseMoment) ^ (1 / power) := by
  have inverseNonnegative : 0 ≤ finiteMean (tupleWeight (fun _ : Fin count => weight))
      (fun input : Fin count → Outcome => ∑ edge, (resistance (input edge))⁻¹ ^ power) := by
    unfold finiteMean
    exact Finset.sum_nonneg (fun input _ => mul_nonneg (tupleWeight_nonnegative _ (fun _ => nonnegative) input)
      (Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive (input edge)).le) _)))
  have summedBound : finiteMean (tupleWeight (fun _ : Fin count => weight))
      (fun input : Fin count → Outcome => ∑ edge, (resistance (input edge))⁻¹ ^ power) ≤
        (count : ℝ) * inverseMoment := by
    have equality := finiteMean_tuple_sum_local (fun _ : Fin count => weight)
      (fun _ outcome => (resistance outcome)⁻¹ ^ power) (fun _ => normalized)
    change finiteMean (tupleWeight (fun _ : Fin count => weight))
      (fun input : Fin count → Outcome => ∑ edge, (resistance (input edge))⁻¹ ^ power) =
        ∑ _edge : Fin count, finiteMean weight (fun outcome => (resistance outcome)⁻¹ ^ power) at equality
    rw [equality]
    calc
      _ ≤ ∑ _edge : Fin count, inverseMoment := Finset.sum_le_sum (fun _ _ => inverseBound)
      _ = _ := by simp
  apply (network.finite_current_fourth_moment_le_inverse_envelope connected
    (tupleWeight (fun _ : Fin count => weight)) (tupleWeight_nonnegative _ (fun _ => nonnegative))
    (tupleWeight_normalized _ (fun _ => normalized)) (fun input edge => resistance (input edge))
    (fun input edge => positive (input edge)) powerAtLeastTwo).trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow inverseNonnegative summedBound (by
      have powerPositive : 0 < power := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) powerAtLeastTwo
      positivity))
  apply Real.rpow_nonneg
  unfold finiteMean
  exact Finset.sum_nonneg (fun input _ =>
    mul_nonneg (tupleWeight_nonnegative _ (fun _ => nonnegative) input) (sq_nonneg _))

theorem finite_electrical_variance_le_product_moments {count : ℕ}
    (network : FiniteNetwork Vertex (Fin count))
    (connected : network.graph.Reachable network.source network.target)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (resistance : Outcome → ℝ) (positive : ∀ outcome, 0 < resistance outcome)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (inverseMoment : ℝ)
    (inverseBound : finiteMean weight (fun outcome => (resistance outcome)⁻¹ ^ power) ≤ inverseMoment) :
    finiteVariance (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → Outcome =>
      network.effectiveResistance (fun edge => resistance (input edge))) ≤
      2 * finiteMean weight (fun outcome => resistance outcome ^ 2) *
      (finiteMean (tupleWeight (fun _ : Fin count => weight)) (fun input : Fin count → Outcome =>
        network.effectiveResistance (fun edge => resistance (input edge))^2)) ^ (1 / (2 : ℝ)) *
        ((count : ℝ) * inverseMoment) ^ (1 / power) := by
  have secondMomentNonnegative : 0 ≤ finiteMean weight (fun outcome => resistance outcome^2) :=
    Finset.sum_nonneg (fun outcome _ => mul_nonneg (nonnegative outcome) (sq_nonneg _))
  have currentBound := network.finite_iid_current_fourth_moment_bound connected weight nonnegative
    normalized resistance positive powerAtLeastTwo inverseMoment inverseBound
  apply (network.finite_electrical_variance_bound connected weight nonnegative normalized resistance positive).trans
  exact (mul_le_mul_of_nonneg_left currentBound (mul_nonneg (by norm_num) secondMomentNonnegative)).trans_eq (by ring)

end
end IGSIII34.Resistance.FiniteNetwork
