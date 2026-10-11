import IGSIII34.Percolation.Continuation.ElectricalBoundaryVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal _root_.Topology

theorem electrical_eigenlaw_generation_boundary_variance_geometric (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) (depth : ℕ) :
    electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth /
        (growth:ℝ)^(2*(depth+1)) ≤
      (2*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
        Real.sqrt (∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
        (∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0))^(1/power)) *
          (((rule.edges:ℝ)^(1/power))/(growth:ℝ))^(depth+1) := by
  have growthRealPositive : 0 < (growth:ℝ) := by exact_mod_cast growthPositive
  have inverseNonnegative : 0 ≤ ∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0) :=
    integral_nonneg (fun value => Real.rpow_nonneg (inv_nonneg.mpr value.property) _)
  have rootEquality :
      ((growth:ℝ)^(2*(depth+1))*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)))^(1/(2:ℝ)) =
        (growth:ℝ)^(depth+1)*Real.sqrt (∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) := by
    have powerEquality : (growth:ℝ)^(2*(depth+1)) = ((growth:ℝ)^(depth+1))^2 := by
      rw [← pow_mul, Nat.mul_comm 2]
    calc
      _ = Real.sqrt ((growth:ℝ)^(2*(depth+1))*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0))) :=
        (Real.sqrt_eq_rpow _).symm
      _ = Real.sqrt ((growth:ℝ)^(2*(depth+1)))*Real.sqrt (∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) :=
        Real.sqrt_mul (pow_nonneg growth.property (2*(depth+1))) _
      _ = _ := by
        rw [powerEquality, Real.sqrt_sq_eq_abs]
        congr 1
        exact abs_of_nonneg (pow_nonneg (show (0:ℝ) ≤ (growth:ℝ) from growth.property) _)
  have bound := electrical_eigenlaw_generation_boundary_variance_bound rule p positive belowOne fixedPoint law lawPositive
    moments growth eigenlaw powerAtLeastTwo depth
  rw [rootEquality, rule.generation_edges, Nat.cast_pow,
    Real.mul_rpow (pow_nonneg (Nat.cast_nonneg rule.edges) _) inverseNonnegative,
    ← Real.rpow_pow_comm (Nat.cast_nonneg rule.edges)] at bound
  apply (div_le_iff₀ (pow_pos growthRealPositive _)).mpr
  refine bound.trans_eq ?_
  rw [div_pow]
  have powerEquality : (growth:ℝ)^(2*(depth+1)) = ((growth:ℝ)^(depth+1))^2 := by
    rw [← pow_mul, Nat.mul_comm 2]
  rw [powerEquality]
  field_simp [growthRealPositive.ne']
  <;> ring

theorem electrical_eigenlaw_generation_boundary_variance_tendsto_zero (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    Tendsto (fun depth => electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth /
      (growth:ℝ)^(2*(depth+1))) atTop (𝓝 0) := by
  have growthRealAboveOne : 1 < (growth:ℝ) := by exact_mod_cast growthAboveOne
  have growthPositive : 0 < growth := zero_lt_one.trans growthAboveOne
  have maximumPositive : 0 < max (1:ℝ) (rule.edges:ℝ) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have rootConvergence : Tendsto (fun power : ℝ => (max (1:ℝ) (rule.edges:ℝ))^(1/power)) atTop (𝓝 1) := by
    have convergence := (Real.continuousAt_const_rpow (b := 0) maximumPositive.ne').tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun power : ℝ => power⁻¹) atTop (𝓝 0))
    simpa only [one_div, Real.rpow_zero, Function.comp_def] using convergence
  obtain ⟨power, powerAtLeastTwo, maximumBound⟩ := (eventually_ge_atTop (2:ℝ)).and
    (rootConvergence.eventually (gt_mem_nhds growthRealAboveOne)) |>.exists
  have powerBound : (rule.edges:ℝ)^(1/power) < (growth:ℝ) :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (le_max_right _ _)
      (div_nonneg zero_le_one (by linarith))).trans_lt maximumBound
  have ratioNonnegative : 0 ≤ (rule.edges:ℝ)^(1/power)/(growth:ℝ) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) growth.property
  have ratioBelowOne : (rule.edges:ℝ)^(1/power)/(growth:ℝ) < 1 :=
    (div_lt_one (by exact_mod_cast growthPositive)).mpr powerBound
  have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioBelowOne
  have shifted := geometric.comp (tendsto_add_atTop_nat 1)
  have upper := shifted.const_mul
    (2*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
      Real.sqrt (∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
      (∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0))^(1/power))
  simp only [mul_zero] at upper
  apply squeeze_zero (fun depth => div_nonneg
    (electricalBoundaryGenerationVariance_nonnegative rule p positive belowOne fixedPoint law depth)
    (pow_nonneg growth.property _))
    (fun depth => electrical_eigenlaw_generation_boundary_variance_geometric rule p positive belowOne fixedPoint law lawPositive
      moments growth growthPositive eigenlaw powerAtLeastTwo depth) upper

end
end IGSIII34.Percolation
