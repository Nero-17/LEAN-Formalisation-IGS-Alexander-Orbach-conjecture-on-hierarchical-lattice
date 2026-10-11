import IGSIII34.Percolation.Continuation.ElectricalBoundaryL1Convergence
import IGSIII34.Percolation.ElectricalContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal BigOperators _root_.Topology

theorem electricalBoundaryTreeShift_preserving (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (address : List (Fin rule.edges)) :
    MeasurePreserving (electricalBoundaryTreeShift rule address)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  refine ⟨electricalBoundaryTreeShift_measurable rule address, ?_⟩
  have injective : Function.Injective (fun coordinate : List (Fin rule.edges) × Bool =>
      (address++coordinate.1, coordinate.2)) := by
    intro first second equality
    change (address++first.1, first.2) = (address++second.1, second.2) at equality
    have addresses : first.1 = second.1 := (List.append_right_injective address) (congrArg Prod.fst equality)
    have states : first.2 = second.2 := by simpa only [Prod.snd] using congrArg Prod.snd equality
    exact Prod.ext addresses states
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law:Measure ℝ≥0)) injective

def electricalBoundaryNormalizedTransfer (rule : Rule) (growth : ℝ≥0)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) → ℝ)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) : ℝ :=
  (growth:ℝ)⁻¹ * electricalCell rule.network (sample ([], true)).1
    (fun edge => max (value (electricalBoundaryTreeShift rule [edge] sample)) 0)

theorem electricalBoundaryNormalizedTransfer_measurable (rule : Rule) (growth : ℝ≥0)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) → ℝ)
    (measurable : Measurable value) : Measurable (electricalBoundaryNormalizedTransfer rule growth value) :=
  measurable_const.mul ((electricalCell_positivePart_dispatch_measurable rule.network).comp
    ((measurable_fst.comp (measurable_pi_apply ([], true))).prodMk
      (measurable_pi_lambda _ (fun edge => measurable.comp (electricalBoundaryTreeShift_measurable rule [edge])))))

theorem electricalBoundaryNormalizedTransfer_eLpNorm_sub_le (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) → ℝ)
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second) :
    eLpNorm (fun sample => electricalBoundaryNormalizedTransfer rule growth first sample -
      electricalBoundaryNormalizedTransfer rule growth second sample) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
      ‖(growth:ℝ)⁻¹‖ₑ*(rule.edges:ℝ≥0∞)*eLpNorm (fun sample => first sample-second sample) 1
        (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  have bound := electrical_random_difference_eLpNorm_le_sum
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) 1 rule.network
    (fun sample => (sample ([], true)).1) le_rfl
    (fun edge sample => first (electricalBoundaryTreeShift rule [edge] sample))
    (fun edge sample => second (electricalBoundaryTreeShift rule [edge] sample))
    (fun edge => (firstMeasurable.comp (electricalBoundaryTreeShift_measurable rule [edge])).aestronglyMeasurable)
    (fun edge => (secondMeasurable.comp (electricalBoundaryTreeShift_measurable rule [edge])).aestronglyMeasurable)
  have sameNorm (edge : Fin rule.edges) : eLpNorm (fun sample =>
      first (electricalBoundaryTreeShift rule [edge] sample)-second (electricalBoundaryTreeShift rule [edge] sample)) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) =
        eLpNorm (fun sample => first sample-second sample) 1
          (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
    exact eLpNorm_comp_measurePreserving (p := 1)
      (g := fun sample => first sample-second sample)
      (f := electricalBoundaryTreeShift rule [edge])
      (firstMeasurable.sub secondMeasurable).aestronglyMeasurable
      (electricalBoundaryTreeShift_preserving rule p positive belowOne fixedPoint law [edge])
  simp_rw [sameNorm] at bound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at bound
  have outputEquality : (fun sample => electricalBoundaryNormalizedTransfer rule growth first sample -
      electricalBoundaryNormalizedTransfer rule growth second sample) =
      (growth:ℝ)⁻¹ • (fun sample => electricalCell rule.network (sample ([], true)).1
        (fun edge => max (first (electricalBoundaryTreeShift rule [edge] sample)) 0) -
          electricalCell rule.network (sample ([], true)).1
            (fun edge => max (second (electricalBoundaryTreeShift rule [edge] sample)) 0)) := by
    funext sample
    simp only [electricalBoundaryNormalizedTransfer, Pi.smul_apply, smul_eq_mul, mul_sub]
  rw [outputEquality, eLpNorm_const_smul]
  exact (mul_le_mul_left' bound _).trans_eq (mul_assoc _ _ _).symm

theorem electricalBoundaryTreeIteration_normalized_recursion (rule : Rule) (growth : ℝ≥0)
    (depth : ℕ) (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :
    (electricalBoundaryTreeIteration rule (depth+2) sample:ℝ)/(growth:ℝ)^(depth+2) =
      electricalBoundaryNormalizedTransfer rule growth
        (fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)) sample := by
  have nonnegative (edge : Fin rule.edges) :
      0 ≤ (electricalBoundaryTreeIteration rule (depth+1) (electricalBoundaryTreeShift rule [edge] sample):ℝ) /
        (growth:ℝ)^(depth+1) := div_nonneg (by positivity) (pow_nonneg growth.property _)
  unfold electricalBoundaryNormalizedTransfer
  simp only [max_eq_left (nonnegative _)]
  change electricalCell rule.network (sample ([], true)).1
    (fun edge => (electricalBoundaryTreeIteration rule (depth+1) (electricalBoundaryTreeShift rule [edge] sample):ℝ)) /
      (growth:ℝ)^(depth+2) = _
  have scaling := electricalCell_scale rule.network (sample ([], true)).1
    (fun edge => show (0:ℝ) ≤ (electricalBoundaryTreeIteration rule (depth+1)
      (electricalBoundaryTreeShift rule [edge] sample):ℝ) from (electricalBoundaryTreeIteration rule (depth+1)
      (electricalBoundaryTreeShift rule [edge] sample)).property)
    (scalar := ((growth:ℝ)^(depth+1))⁻¹) (inv_nonneg.mpr (pow_nonneg growth.property _))
  have equality : (fun edge : Fin rule.edges => (electricalBoundaryTreeIteration rule (depth+1)
      (electricalBoundaryTreeShift rule [edge] sample):ℝ)/(growth:ℝ)^(depth+1)) =
      (fun edge => ((growth:ℝ)^(depth+1))⁻¹*(electricalBoundaryTreeIteration rule (depth+1)
        (electricalBoundaryTreeShift rule [edge] sample):ℝ)) := by
    funext edge
    simp only [div_eq_mul_inv, mul_comm]
  rw [equality, scaling, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem electricalBoundaryNormalizedTransfer_fixed_of_raw_L1_limit (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) → ℝ)
    (valueMeasurable : Measurable value)
    (convergence : Tendsto (fun depth => eLpNorm
      (fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)-value sample) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)) atTop (𝓝 0)) :
    value =ᵐ[electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
      electricalBoundaryNormalizedTransfer rule growth value := by
  let sequence (depth : ℕ) (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :=
    (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)
  have sequenceMeasurable (depth : ℕ) : Measurable (sequence depth) :=
    (NNReal.continuous_coe.measurable.comp (electricalBoundaryTreeIteration_measurable rule (depth+1))).div_const _
  have outputMeasurable := electricalBoundaryNormalizedTransfer_measurable rule growth value valueMeasurable
  have errorBound (depth : ℕ) : eLpNorm (fun sample => value sample-electricalBoundaryNormalizedTransfer rule growth value sample) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
      eLpNorm (fun sample => sequence (depth+1) sample-value sample) 1
        (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) +
        ‖(growth:ℝ)⁻¹‖ₑ*(rule.edges:ℝ≥0∞)*eLpNorm (fun sample => sequence depth sample-value sample) 1
          (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
    have decomposition : (fun sample => value sample-electricalBoundaryNormalizedTransfer rule growth value sample) =
        (fun sample => value sample-sequence (depth+1) sample) +
          (fun sample => sequence (depth+1) sample-electricalBoundaryNormalizedTransfer rule growth value sample) := by
      funext sample
      simp only [Pi.add_apply]
      ring
    rw [decomposition]
    refine (eLpNorm_add_le ((valueMeasurable.sub (sequenceMeasurable (depth+1))).aestronglyMeasurable)
      (((sequenceMeasurable (depth+1)).sub outputMeasurable).aestronglyMeasurable) le_rfl).trans ?_
    have firstEquality : eLpNorm (fun sample => value sample-sequence (depth+1) sample) 1
        (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) =
        eLpNorm (fun sample => sequence (depth+1) sample-value sample) 1
          (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) :=
      eLpNorm_sub_comm _ _ _ _
    change eLpNorm (fun sample => value sample-sequence (depth+1) sample) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) +
      eLpNorm (fun sample => sequence (depth+1) sample-electricalBoundaryNormalizedTransfer rule growth value sample) 1
        (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤ _
    rw [firstEquality]
    refine add_le_add le_rfl ?_
    have recursion : sequence (depth+1) = electricalBoundaryNormalizedTransfer rule growth (sequence depth) := by
      funext sample
      exact electricalBoundaryTreeIteration_normalized_recursion rule growth depth sample
    rw [recursion]
    exact electricalBoundaryNormalizedTransfer_eLpNorm_sub_le rule p positive belowOne fixedPoint law growth
      (sequence depth) value (sequenceMeasurable depth) valueMeasurable
  have upper := (convergence.comp (tendsto_add_atTop_nat 1)).add
    (ENNReal.Tendsto.const_mul (a := ‖(growth:ℝ)⁻¹‖ₑ*(rule.edges:ℝ≥0∞)) convergence
      (Or.inr (ENNReal.mul_ne_top enorm_ne_top (ENNReal.natCast_ne_top rule.edges))))
  simp only [mul_zero, add_zero] at upper
  have zeroNorm : eLpNorm (fun sample => value sample-electricalBoundaryNormalizedTransfer rule growth value sample) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) = 0 :=
    le_antisymm (ge_of_tendsto' upper errorBound) bot_le
  have differenceZero := (eLpNorm_eq_zero_iff (valueMeasurable.sub outputMeasurable).aestronglyMeasurable
    (by norm_num : (1:ℝ≥0∞) ≠ 0)).mp zeroNorm
  filter_upwards [differenceZero] with sample zero
  exact sub_eq_zero.mp zero

end
end IGSIII34.Percolation
