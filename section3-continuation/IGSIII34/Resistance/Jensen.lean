import IGSIII34.Resistance.Continuity
import IGSIII34.Resistance.Conductance

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem weighted_mean_mul_reciprocal_mean_ge_one
    {Index : Type*} [Fintype Index] (weight value : Index → ℝ)
    (weightNonnegative : ∀ index, 0 ≤ weight index) (weightSum : ∑ index, weight index = 1)
    (valuePositive : ∀ index, 0 < value index) :
    1 ≤ (∑ index, weight index * value index) * (∑ index, weight index / value index) := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun index => Real.sqrt (weight index) * Real.sqrt (value index))
    (fun index => Real.sqrt (weight index) / Real.sqrt (value index))
  have productIdentity (index : Index) :
      (Real.sqrt (weight index) * Real.sqrt (value index)) *
        (Real.sqrt (weight index) / Real.sqrt (value index)) = weight index := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (valuePositive index))]
    exact Real.sq_sqrt (weightNonnegative index)
  have firstSquare (index : Index) :
      (Real.sqrt (weight index) * Real.sqrt (value index)) ^ 2 = weight index * value index := by
    rw [mul_pow, Real.sq_sqrt (weightNonnegative index), Real.sq_sqrt (valuePositive index).le]
  have secondSquare (index : Index) :
      (Real.sqrt (weight index) / Real.sqrt (value index)) ^ 2 = weight index / value index := by
    rw [div_pow, Real.sq_sqrt (weightNonnegative index), Real.sq_sqrt (valuePositive index).le]
  simpa only [productIdentity, firstSquare, secondSquare, weightSum, one_pow] using cauchy

theorem conductanceFunctional_constant (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {scalar : ℝ} (scalarPositive : 0 < scalar) :
    network.conductanceFunctional (fun _ => scalar) =
      scalar / network.effectiveResistance (fun _ => 1) := by
  rw [network.conductanceFunctional_eq_reciprocalResistance connected (fun _ => scalarPositive)]
  have scale := network.effectiveResistance_scale
    (network.unitFlows_nonempty_of_connected connected) (resistance := fun _ => 1)
    (fun _ => zero_le_one) (inv_nonneg.mpr scalarPositive.le)
  simp only [mul_one] at scale
  rw [scale]
  field_simp

theorem mean_reciprocalResistance_upper_bound
    {Index : Type*} [Fintype Index] (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (weight : Index → ℝ) (weightNonnegative : ∀ index, 0 ≤ weight index)
    (resistance : Index → Edge → ℝ) (resistancePositive : ∀ index edge, 0 < resistance index edge)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, ∑ index, weight index * (resistance index edge)⁻¹ = inverseMean) :
    ∑ index, weight index / network.effectiveResistance (resistance index) ≤
      inverseMean / network.effectiveResistance (fun _ => 1) := by
  have bound := network.conductanceFunctional_weighted_sum_lower_bound weight weightNonnegative
    (fun index edge => (resistance index edge)⁻¹)
    (fun index edge => inv_nonneg.mpr (resistancePositive index edge).le)
  have outputIdentity (index : Index) :
      network.conductanceFunctional (fun edge => (resistance index edge)⁻¹) =
        1 / network.effectiveResistance (resistance index) := by
    rw [network.conductanceFunctional_eq_reciprocalResistance connected
      (fun edge => inv_pos.mpr (resistancePositive index edge))]
    simp only [inv_inv]
  have inputIdentity : (fun edge => ∑ index, weight index * (resistance index edge)⁻¹) =
      (fun _ : Edge => inverseMean) := funext commonInverseMean
  simpa only [outputIdentity, inputIdentity,
    network.conductanceFunctional_constant connected inverseMeanPositive, mul_one_div] using bound

theorem finite_random_resistance_mean_sandwich
    {Index : Type*} [Fintype Index] (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (weight : Index → ℝ) (weightNonnegative : ∀ index, 0 ≤ weight index)
    (weightSum : ∑ index, weight index = 1)
    (resistance : Index → Edge → ℝ) (resistancePositive : ∀ index edge, 0 < resistance index edge)
    (commonMean : ∀ edge, ∑ index, weight index * resistance index edge = 1)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, ∑ index, weight index * (resistance index edge)⁻¹ = inverseMean) :
    network.effectiveResistance (fun _ => 1) / inverseMean ≤
      ∑ index, weight index * network.effectiveResistance (resistance index) ∧
    ∑ index, weight index * network.effectiveResistance (resistance index) ≤
      network.effectiveResistance (fun _ => 1) := by
  have unitResistancePositive := network.effectiveResistance_pos_of_connected connected (fun _ => zero_lt_one)
  have outputPositive (index : Index) : 0 < network.effectiveResistance (resistance index) :=
    network.effectiveResistance_pos_of_connected connected (resistancePositive index)
  have averageNonnegative : 0 ≤ ∑ index, weight index * network.effectiveResistance (resistance index) :=
    Finset.sum_nonneg (fun index _ => mul_nonneg (weightNonnegative index) (outputPositive index).le)
  have cauchy := weighted_mean_mul_reciprocal_mean_ge_one weight
    (fun index => network.effectiveResistance (resistance index)) weightNonnegative weightSum outputPositive
  have reciprocalBound := network.mean_reciprocalResistance_upper_bound connected weight
    weightNonnegative resistance resistancePositive inverseMeanPositive commonInverseMean
  have productBound := cauchy.trans (mul_le_mul_of_nonneg_left reciprocalBound averageNonnegative)
  constructor
  · apply (div_le_iff₀ inverseMeanPositive).mpr
    have cleared := (le_div_iff₀ unitResistancePositive).mp
      (show 1 ≤ ((∑ index, weight index * network.effectiveResistance (resistance index)) * inverseMean) /
        network.effectiveResistance (fun _ => 1) by simpa only [mul_div_assoc] using productBound)
    simpa only [one_mul, mul_comm] using cleared
  · have inputIdentity : (fun edge => ∑ index, weight index * resistance index edge) =
        (fun _ : Edge => 1) := funext commonMean
    simpa only [inputIdentity] using network.effectiveResistance_weighted_sum_lower_bound
      (network.unitFlows_nonempty_of_connected connected) weight weightNonnegative resistance
      (fun index edge => (resistancePositive index edge).le)

end
end IGSIII34.Resistance.FiniteNetwork
