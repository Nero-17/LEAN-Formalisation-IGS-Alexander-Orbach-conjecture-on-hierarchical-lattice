import IGSIII34.Percolation.Continuation.ElectricalBoundaryEndogenousLimit
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

theorem electrical_square_integral_zero_implies_tendstoInMeasure
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (sequence : ℕ → Sample → ℝ) (membership : ∀ depth, MemLp (sequence depth) 2 measure)
    (convergence : Tendsto (fun depth => ∫ sample, (sequence depth sample)^2 ∂measure) atTop (𝓝 0)) :
    TendstoInMeasure measure sequence atTop (fun _ => 0) := by
  have normSquare (depth : ℕ) : ‖(membership depth).toLp (sequence depth)‖^2 =
      ∫ sample, (sequence depth sample)^2 ∂measure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(membership depth).coeFn_toLp] with sample equality
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [equality]
  have normEquality (depth : ℕ) : ‖(membership depth).toLp (sequence depth)‖ =
      Real.sqrt (∫ sample, (sequence depth sample)^2 ∂measure) := by
    rw [← normSquare depth, Real.sqrt_sq (norm_nonneg _)]
  have normConvergence : Tendsto (fun depth => ‖(membership depth).toLp (sequence depth)‖) atTop (𝓝 0) := by
    simp_rw [normEquality]
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp convergence
  have lpConvergence : Tendsto (fun depth => (membership depth).toLp (sequence depth)) atTop
      (𝓝 (0: Lp ℝ 2 measure)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero] using normConvergence
  exact (tendstoInMeasure_of_tendsto_Lp lpConvergence).congr
    (fun depth => (membership depth).coeFn_toLp) (Lp.coeFn_zero _ _ _)

theorem electricalBoundaryTreeIteration_centered_tendstoInMeasure_zero (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    TendstoInMeasure (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (fun depth sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1) -
        electricalBoundaryMeanProcess rule law growth depth sample) atTop (fun _ => 0) := by
  have secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_two] using moments 2
  have lawMemLp := (memLp_two_iff_integrable_sq NNReal.continuous_coe.measurable.aestronglyMeasurable).mpr secondMoment
  have meanMemLp (depth : ℕ) : MemLp (electricalBoundaryMeanProcess rule law growth depth) 2
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
    refine ⟨((electricalBoundaryMeanProcess_stronglyAdapted rule law growth depth).mono
      ((electricalBoundaryMarksPrefixFiltration rule).le depth)).aestronglyMeasurable, ?_⟩
    exact (electricalBoundaryMeanProcess_eLpNorm_two_bound rule p positive belowOne fixedPoint law lawPositive
      secondMoment growth (zero_lt_one.trans growthAboveOne) eigenlaw depth).trans_lt lawMemLp.eLpNorm_lt_top
  have normalizedMemLp (depth : ℕ) : MemLp (fun sample =>
      (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)) 2
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
    simpa only [div_eq_mul_inv] using (electricalBoundaryTreeIteration_eigenlaw_memLp rule p positive belowOne fixedPoint
      law secondMoment growth eigenlaw (depth+1)).mul_const (((growth:ℝ)^(depth+1))⁻¹)
  apply electrical_square_integral_zero_implies_tendstoInMeasure
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) _
    (fun depth => (normalizedMemLp depth).sub (meanMemLp depth))
  exact electricalBoundaryTreeIteration_normalized_centered_square_tendsto_zero rule p positive belowOne fixedPoint
    law lawPositive moments growth growthAboveOne eigenlaw

theorem electrical_tendstoInMeasure_of_centered_and_ae_limit
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence centers : ℕ → Sample → ℝ) (value : Sample → ℝ)
    (measurable : ∀ depth, AEStronglyMeasurable (sequence depth) measure)
    (errorConvergence : TendstoInMeasure measure (fun depth sample => sequence depth sample-centers depth sample)
      atTop (fun _ => 0))
    (centerConvergence : ∀ᵐ sample ∂measure, Tendsto (fun depth => centers depth sample) atTop (𝓝 (value sample))) :
    TendstoInMeasure measure sequence atTop value := by
  apply (exists_seq_tendstoInMeasure_atTop_iff measurable).mpr
  intro subsequence increasing
  obtain ⟨subsubsequence, subIncreasing, errorLimit⟩ :=
    (errorConvergence.comp increasing.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨subsubsequence, subIncreasing, ?_⟩
  filter_upwards [errorLimit, centerConvergence] with sample errorLimit centerLimit
  have convergence := errorLimit.add (centerLimit.comp (increasing.tendsto_atTop.comp subIncreasing.tendsto_atTop))
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using convergence

end
end IGSIII34.Percolation
