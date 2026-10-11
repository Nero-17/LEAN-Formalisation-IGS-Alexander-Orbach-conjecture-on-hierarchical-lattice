import IGSIII34.Percolation.Continuation.ElectricalSimpleLawVariance
import IGSIII34.Percolation.Continuation.ElectricalBoundaryOutputApproximation
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators _root_.Topology
attribute [local irreducible] electricalSimpleBoundary

theorem electricalCell_law_variance_le_product_moments {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : network.crosses configuration = true)
    (law : ProbabilityMeasure ℝ≥0) (positive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) :
    (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ))^2
      ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) -
      (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ))
        ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)))^2 ≤
      2*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
        (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ))^2
          ∂Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)))^(1/(2:ℝ)) *
        ((edges:ℝ)*(∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0)))^(1/power) := by
  let measure := Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))
  let response (index : ℕ) (input : Fin edges → ℝ≥0) :=
    electricalCell network configuration (fun edge => electricalSimpleBoundary index (input edge))
  have responseMeasurable (index : ℕ) : Measurable (response index) := by
    have approximationMeasurable : Measurable ((electricalSimpleBoundary index) : ℝ≥0 → ℝ) :=
      (electricalSimpleBoundary index).measurable
    exact electricalCell_measurable (Outcome := Fin edges → ℝ≥0) network
      (fun _ : Fin edges → ℝ≥0 => configuration) measurable_const
      (fun (input : Fin edges → ℝ≥0) edge => electricalSimpleBoundary index (input edge))
      (measurable_pi_lambda _ (fun edge => approximationMeasurable.comp (measurable_pi_apply edge)))
      (fun input edge => (electricalSimpleBoundary_positive index (input edge)).le)
  have responseMemLp (index : ℕ) : MemLp (response index) 2 measure := by
    obtain ⟨bound, bounds⟩ := (electricalSimpleBoundary index).exists_forall_norm_le
    apply memLp_of_bounded (a := 0) (b := (edges:ℝ)*bound) _ (responseMeasurable index).aestronglyMeasurable 2
    filter_upwards [] with input
    refine ⟨(IGSIII34.Percolation.network network configuration).effectiveResistance_nonnegative_all
      (fun edge => (electricalSimpleBoundary_positive index (input edge.val)).le), ?_⟩
    apply (electricalCell_le_sum network configuration (fun edge => (electricalSimpleBoundary_positive index (input edge)).le)).trans
    calc
      _ ≤ ∑ _edge : Fin edges, bound := Finset.sum_le_sum (fun edge _ =>
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using bounds (input edge)))
      _ = _ := by simp
  have centralEquality (index : ℕ) :
      (∫ input, (response index input-∫ input, response index input ∂measure)^2 ∂measure) =
      (∫ input, response index input^2 ∂measure)-(∫ input, response index input ∂measure)^2 := by
    rw [← variance_eq_integral (responseMeasurable index).aemeasurable, variance_eq_sub (responseMemLp index)]
    rfl
  have estimates (index : ℕ) := simpleFunc_electricalCell_variance_le_product_moments (law:Measure ℝ≥0)
    network configuration crosses (electricalSimpleBoundary index) (electricalSimpleBoundary_positive index)
    powerAtLeastTwo (∫ value, (electricalSimpleBoundary index value)⁻¹^power ∂(law:Measure ℝ≥0)) le_rfl
  have meanConvergence : Tendsto (fun index => ∫ input, response index input ∂measure) atTop
      (𝓝 (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ)) ∂measure)) := by
    simpa only [pow_one] using electricalCell_simpleBoundary_moment_tendsto network configuration law positive moments 1 (by norm_num) (by norm_num)
  have secondConvergence := electricalCell_simpleBoundary_moment_tendsto network configuration law positive moments 2 (by norm_num) (by norm_num)
  have boundarySecondConvergence := electricalSimpleBoundary_real_moments_tendsto law positive moments 2
  simp only [Real.rpow_two] at boundarySecondConvergence
  have inverseConvergence : Tendsto (fun index => ∫ value, (electricalSimpleBoundary index value)⁻¹^power ∂(law:Measure ℝ≥0))
      atTop (𝓝 (∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0))) := by
    simpa only [Real.rpow_neg_eq_inv_rpow] using electricalSimpleBoundary_real_moments_tendsto law positive moments (-power)
  have squareRootConvergence := (Real.continuousAt_rpow_const
    (∫ input : Fin edges → ℝ≥0, electricalCell network configuration (fun edge => (input edge:ℝ))^2 ∂measure)
    (1/(2:ℝ)) (Or.inr (by norm_num))).tendsto.comp secondConvergence
  have inversePowerNonnegative : 0 ≤ 1/power := div_nonneg zero_le_one (by linarith)
  have inverseRootConvergence := (Real.continuousAt_rpow_const
    ((edges:ℝ)*(∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0)))
    (1/power) (Or.inr inversePowerNonnegative)).tendsto.comp (inverseConvergence.const_mul (edges:ℝ))
  apply le_of_tendsto_of_tendsto (secondConvergence.sub (meanConvergence.pow 2))
    (((boundarySecondConvergence.const_mul 2).mul squareRootConvergence).mul inverseRootConvergence)
  apply Eventually.of_forall
  intro index
  have estimate := estimates index
  change (∫ input, (response index input-∫ input, response index input ∂measure)^2 ∂measure) ≤ _ at estimate
  rw [centralEquality index] at estimate
  exact estimate

end
end IGSIII34.Percolation

