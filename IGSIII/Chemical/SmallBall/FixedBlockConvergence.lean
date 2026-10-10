import IGSIII.Chemical.SmallBall.NormalizedPairedBarrier
import IGSIII.Chemical.SmallBall.PairedUniformBarrier
import IGSIII.Chemical.ChemicalOmega
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Set Filter
open scoped ENNReal Topology

noncomputable section

theorem chemicalOrbit_eventually_between_of_fixed_block (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedIdentity : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed)
    (lower upper : ℝ) (lowerNonnegative : 0 ≤ lower) (block : ℕ)
    {parameter ratio : ℝ} (parameterPositive : 0 < parameter) (ratioNonnegative : 0 ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1)
    (upperIntegrable : Integrable (fun marks => Real.exp (parameter *
      (chemicalOrbit rule p positive lessOne fixedPoint growth block marks - upper * fixed marks)))
      (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperBound : (∫ marks, Real.exp (parameter *
      (chemicalOrbit rule p positive lessOne fixedPoint growth block marks - upper * fixed marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio)
    (lowerIntegrable : Integrable (fun marks => Real.exp (parameter *
      (lower * fixed marks - chemicalOrbit rule p positive lessOne fixedPoint growth block marks)))
      (independentInnovationLaw rule p positive lessOne fixedPoint))
    (lowerBound : (∫ marks, Real.exp (parameter *
      (lower * fixed marks - chemicalOrbit rule p positive lessOne fixedPoint growth block marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, ∀ᶠ depth : ℕ in atTop,
      lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ∧
      chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ≤ upper * fixed marks := by
  have lowerEquality : (fun marks => Real.exp (parameter *
      ((lower • fixed) marks - (1 : ℝ) * chemicalOrbit rule p positive lessOne fixedPoint growth block marks))) =ᵐ[
        independentInnovationLaw rule p positive lessOne fixedPoint]
      fun marks => Real.exp (parameter * (lower * fixed marks -
        chemicalOrbit rule p positive lessOne fixedPoint growth block marks)) := by
    filter_upwards [Lp.coeFn_smul lower fixed] with marks equality
    rw [equality, Pi.smul_apply, smul_eq_mul, one_mul]
  have probabilities (depth : ℕ) :
      (independentInnovationLaw rule p positive lessOne fixedPoint).real
        {marks | ¬ (lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ∧
          chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ≤ upper * fixed marks)} ≤
      2 * (((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio)) := by
    have upperProbability := normalizedChemicalTransferLp_iterate_paired_comparison_bound_parameter rule classical
      p positive lessOne fixedPoint growth growthPositive
      (chemicalOrbit rule p positive lessOne fixedPoint growth block) fixed parameterPositive ratioNonnegative
      upperIntegrable upperBound geometricBelowOne depth
    have lowerProbability := normalizedChemicalTransferLp_iterate_paired_comparison_bound_parameter rule classical
      p positive lessOne fixedPoint growth growthPositive (lower • fixed)
      (chemicalOrbit rule p positive lessOne fixedPoint growth block) parameterPositive ratioNonnegative
      (lowerIntegrable.congr lowerEquality.symm) (by rwa [integral_congr_ae lowerEquality]) geometricBelowOne depth
    rw [Function.iterate_fixed fixedIdentity, show
      (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1]
        (chemicalOrbit rule p positive lessOne fixedPoint growth block) =
          chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) from
        (Function.iterate_add_apply _ (depth + 1) block _).symm] at upperProbability
    rw [normalizedChemicalTransferLp_iterate_smul rule p positive lessOne fixedPoint growth lower lowerNonnegative,
      Function.iterate_fixed fixedIdentity, show
      (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1]
        (chemicalOrbit rule p positive lessOne fixedPoint growth block) =
          chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) from
        (Function.iterate_add_apply _ (depth + 1) block _).symm] at lowerProbability
    have equality : {marks | ¬ (lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ∧
        chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ≤ upper * fixed marks)} =ᵐ[
        independentInnovationLaw rule p positive lessOne fixedPoint]
        (Set.union {marks | upper * fixed marks < chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks}
        {marks | (1 : ℝ) * chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks < (lower • fixed) marks}) := by
      filter_upwards [Lp.coeFn_smul lower fixed] with marks scalarEquality
      apply propext
      change (¬ (lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ∧
        chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ≤ upper * fixed marks)) ↔
        (upper * fixed marks < chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ∨
        1 * chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks < (lower • fixed) marks)
      rw [scalarEquality, Pi.smul_apply, smul_eq_mul, one_mul]
      simp only [not_and_or, not_le]
      exact or_comm
    rw [measureReal_congr equality]
    exact (measureReal_union_le _ _).trans (by linarith)
  have summable := ((summable_nat_add_iff 1).mpr
    ((geometric_power_geometric_summable classical.scale
      (mul_nonneg (Nat.cast_nonneg _) ratioNonnegative) geometricBelowOne).div_const
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio))).mul_left 2
  have finiteEvents : (∑' depth : ℕ, (independentInnovationLaw rule p positive lessOne fixedPoint)
      {marks | ¬ (lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ∧
        chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1 + block) marks ≤ upper * fixed marks)}) ≠ ∞ := by
    apply ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro depth
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (probabilities depth)
  filter_upwards [ae_eventually_notMem finiteEvents] with marks eventual
  have shifted : ∀ᶠ depth : ℕ in atTop,
      lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (depth + (block + 1)) marks ∧
      chemicalOrbit rule p positive lessOne fixedPoint growth (depth + (block + 1)) marks ≤ upper * fixed marks := by
    simpa only [Set.mem_setOf_eq, not_not, Nat.add_assoc, Nat.add_comm 1 block] using eventual
  have mapped : ∀ᶠ depth : ℕ in Filter.map (fun index : ℕ => index + (block + 1)) atTop,
      lower * fixed marks ≤ chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ∧
      chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ≤ upper * fixed marks :=
    Filter.eventually_map.mpr shifted
  rwa [Filter.map_add_atTop_eq_nat] at mapped

theorem ae_tendsto_of_countable_eventual_sandwich
    {Sample : Type*} [MeasurableSpace Sample] (μ : Measure Sample)
    (sequence : ℕ → Sample → ℝ) (fixed : Sample → ℝ) (amplitude : ℝ)
    (sandwiches : ∀ index : ℕ, ∀ᵐ sample ∂μ, ∀ᶠ depth : ℕ in atTop,
      (amplitude - amplitude / ((index + 2 : ℕ) : ℝ)) * fixed sample ≤ sequence depth sample ∧
      sequence depth sample ≤ (amplitude + amplitude / ((index + 2 : ℕ) : ℝ)) * fixed sample) :
    ∀ᵐ sample ∂μ, Tendsto (fun depth => sequence depth sample) atTop (𝓝 (amplitude * fixed sample)) := by
  filter_upwards [ae_all_iff.mpr sandwiches] with sample bounds
  have errors : Tendsto (fun index : ℕ => amplitude / ((index + 2 : ℕ) : ℝ) * fixed sample) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat amplitude)).mul_const (fixed sample)
  apply tendsto_order.2
  constructor
  · intro below belowLimit
    obtain ⟨index, small⟩ := (errors.eventually (gt_mem_nhds (sub_pos.mpr belowLimit))).exists
    exact (bounds index).mono (fun depth inequalities => by nlinarith [inequalities.1])
  · intro above limitBelow
    obtain ⟨index, small⟩ := (errors.eventually (gt_mem_nhds (sub_pos.mpr limitBelow))).exists
    exact (bounds index).mono (fun depth inequalities => by nlinarith [inequalities.2])
end
end IGSIII.Chemical.SmallBall