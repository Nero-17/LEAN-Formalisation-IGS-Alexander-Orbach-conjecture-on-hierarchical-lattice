import IGSIII34.Percolation.Continuation.ElectricalSimpleBoundary
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Filter
open scoped NNReal ENNReal BigOperators _root_.Topology
attribute [local irreducible] electricalSimpleBoundary

theorem electricalCell_simpleBoundary_power_bound {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ≥0) (positive : ∀ edge, 0 < input edge)
    (index power : ℕ) (powerPositive : 0 < power) (powerAtMostTwo : power ≤ 2) :
    ‖(electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge)))^power‖ ≤
      (edges:ℝ)^(power-1)*∑ edge,
        ((input edge:ℝ)^(2*(power:ℝ))+(input edge:ℝ)^(-2*(power:ℝ))) := by
  have cellNonnegative : 0 ≤ electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge)) :=
    (IGSIII34.Percolation.network network configuration).effectiveResistance_nonnegative_all
      (fun edge => (electricalSimpleBoundary_positive index (input edge.val)).le)
  have cellBound := electricalCell_le_sum network configuration (fun edge => (electricalSimpleBoundary_positive index (input edge)).le)
  have boundaryBound (edge : Fin edges) := electricalSimpleBoundary_rpow_bound index (input edge) (positive edge) (power:ℝ)
  have powerCases : power=1 ∨ power=2 := by omega
  rcases powerCases with rfl | rfl
  · simp only [Real.norm_eq_abs, pow_one, abs_of_nonneg cellNonnegative, Nat.sub_self, pow_zero, one_mul]
    apply cellBound.trans
    apply Finset.sum_le_sum
    intro edge _
    simpa only [Nat.cast_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos (electricalSimpleBoundary_positive index (input edge)), abs_one, mul_one] using boundaryBound edge
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have squareBound : (∑ edge, electricalSimpleBoundary index (input edge))^2 ≤
        (edges:ℝ)*∑ edge, (electricalSimpleBoundary index (input edge))^2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ (fun _ : Fin edges => 1)
          (fun edge => electricalSimpleBoundary index (input edge))
    apply ((pow_le_pow_left₀ cellNonnegative cellBound 2).trans squareBound).trans
    simp only [Nat.reduceSub, pow_one]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro edge _
    simpa only [Nat.cast_ofNat, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (electricalSimpleBoundary index (input edge))),
      abs_of_pos (by norm_num : (0:ℝ)<2)] using boundaryBound edge

theorem electricalCell_simpleBoundary_moment_tendsto {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (law : ProbabilityMeasure ℝ≥0) (positive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (power : ℕ) (powerPositive : 0 < power) (powerAtMostTwo : power ≤ 2) :
    Tendsto (fun index => ∫ input : Fin edges → ℝ≥0,
        (electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge)))^power
        ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) atTop
      (𝓝 (∫ input : Fin edges → ℝ≥0, (electricalCell network configuration (fun edge => (input edge:ℝ)))^power
        ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)))) := by
  have inputPositive : ∀ᵐ input : Fin edges → ℝ≥0 ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)),
      ∀ edge, 0 < input edge := ae_all_iff.mpr (fun edge =>
    (measurePreserving_eval (fun _ : Fin edges => (law:Measure ℝ≥0)) edge).quasiMeasurePreserving.ae positive)
  have dominationIntegrable : Integrable (fun input : Fin edges → ℝ≥0 =>
      (edges:ℝ)^(power-1)*∑ edge,
        ((input edge:ℝ)^(2*(power:ℝ))+(input edge:ℝ)^(-2*(power:ℝ))))
        (Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro edge _
    exact (measurePreserving_eval (fun _ : Fin edges => (law:Measure ℝ≥0)) edge).integrable_comp_of_integrable
      ((moments _).add (moments _))
  refine tendsto_integral_of_dominated_convergence
    (F := fun index (input : Fin edges → ℝ≥0) =>
      (electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge)))^power)
    (f := fun input : Fin edges → ℝ≥0 => electricalCell network configuration (fun edge => (input edge:ℝ))^power)
    _ ?_ dominationIntegrable
    (fun index => inputPositive.mono (fun input positive =>
      electricalCell_simpleBoundary_power_bound network configuration input positive index power powerPositive powerAtMostTwo)) ?_
  · intro index
    have approximationMeasurable : Measurable ((electricalSimpleBoundary index) : ℝ≥0 → ℝ) :=
      (electricalSimpleBoundary index).measurable
    have inputsMeasurable : Measurable (fun input : Fin edges → ℝ≥0 =>
        fun edge => electricalSimpleBoundary index (input edge)) :=
      measurable_pi_lambda _ (fun edge => approximationMeasurable.comp (measurable_pi_apply edge))
    have responseMeasurable : Measurable (fun input : Fin edges → ℝ≥0 =>
        electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge))) :=
      electricalCell_measurable (Outcome := Fin edges → ℝ≥0) network
      (fun _ : Fin edges → ℝ≥0 => configuration) measurable_const
      (fun (input : Fin edges → ℝ≥0) edge => electricalSimpleBoundary index (input edge))
      inputsMeasurable
      (fun input edge => (electricalSimpleBoundary_positive index (input edge)).le)
    exact (responseMeasurable.pow_const power).aestronglyMeasurable
  · filter_upwards [inputPositive] with input positive
    have inputsConverge : Tendsto (fun index =>
        (⟨fun edge => electricalSimpleBoundary index (input edge),
          fun edge => (electricalSimpleBoundary_positive index (input edge)).le⟩ :
            {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge})) atTop
        (𝓝 (⟨fun edge => (input edge:ℝ), fun edge => (input edge).property⟩ :
          {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge})) :=
      tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr (fun edge => electricalSimpleBoundary_tendsto (input edge) (positive edge)))
    exact ((electricalCell_continuous_nonnegative network configuration).continuousAt.tendsto.comp inputsConverge).pow power

end
end IGSIII34.Percolation

