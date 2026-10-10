import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII.Probability

open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem exists_countable_lp2_infimum {Sample Index : Type*}
    [MeasurableSpace Sample] [Countable Index] [Nonempty Index]
    (measure : Measure Sample) (family : Index → Lp ℝ 2 measure)
    (lower : Lp ℝ 2 measure) (lowerNonnegative : 0 ≤ lower)
    (lowerBound : ∀ index, lower ≤ family index) :
    ∃ infimum : Lp ℝ 2 measure,
      infimum =ᵐ[measure] (fun sample => ⨅ index, family index sample) ∧
      lower ≤ infimum ∧ IsGLB (Set.range family) infimum := by
  classical
  have bounds : ∀ᵐ sample ∂measure, ∀ index, lower sample ≤ family index sample :=
    ae_all_iff.mpr (fun index => (Lp.coeFn_le lower (family index)).mpr (lowerBound index))
  have nonnegative : ∀ᵐ sample ∂measure, 0 ≤ lower sample :=
    (Lp.coeFn_nonneg lower).mpr lowerNonnegative
  have boundedBelow : ∀ᵐ sample ∂measure,
      BddBelow (Set.range (fun index => family index sample)) := by
    filter_upwards [bounds] with sample sampleBounds
    exact ⟨lower sample, by rintro _ ⟨index, rfl⟩; exact sampleBounds index⟩
  have infimumMeasurable : AEStronglyMeasurable
      (fun sample => ⨅ index, family index sample) measure :=
    (AEMeasurable.iInf (fun index => (Lp.aestronglyMeasurable (family index)).aemeasurable)).aestronglyMeasurable
  let selected : Index := Classical.choice inferInstance
  have infimumMemLp : MemLp (fun sample => ⨅ index, family index sample) 2 measure := by
    apply (Lp.memLp (family selected)).mono' infimumMeasurable
    filter_upwards [bounds, nonnegative, boundedBelow] with sample sampleBounds sampleNonnegative sampleBounded
    rw [Real.norm_eq_abs, abs_of_nonneg (sampleNonnegative.trans (le_ciInf sampleBounds))]
    exact ciInf_le sampleBounded selected
  let infimum : Lp ℝ 2 measure := infimumMemLp.toLp (fun sample => ⨅ index, family index sample)
  have representative : infimum =ᵐ[measure] (fun sample => ⨅ index, family index sample) :=
    MemLp.coeFn_toLp infimumMemLp
  refine ⟨infimum, representative, ?_, ?_⟩
  · apply (Lp.coeFn_le lower infimum).mp
    filter_upwards [representative, bounds] with sample sampleRepresentative sampleBounds
    rw [sampleRepresentative]
    exact le_ciInf sampleBounds
  · constructor
    · rintro _ ⟨index, rfl⟩
      apply (Lp.coeFn_le infimum (family index)).mp
      filter_upwards [representative, boundedBelow] with sample sampleRepresentative sampleBounded
      rw [sampleRepresentative]
      exact ciInf_le sampleBounded index
    · intro candidate candidateBounds
      apply (Lp.coeFn_le candidate infimum).mp
      have candidateBoundsAe : ∀ᵐ sample ∂measure, ∀ index, candidate sample ≤ family index sample :=
        ae_all_iff.mpr (fun index => (Lp.coeFn_le candidate (family index)).mpr
          (candidateBounds (Set.mem_range_self index)))
      filter_upwards [representative, candidateBoundsAe] with sample sampleRepresentative sampleBounds
      rw [sampleRepresentative]
      exact le_ciInf sampleBounds

theorem exists_countable_set_lp2_isGLB {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (family : Set (Lp ℝ 2 measure))
    (familyCountable : family.Countable) (familyNonempty : family.Nonempty)
    (lower : Lp ℝ 2 measure) (lowerNonnegative : 0 ≤ lower)
    (lowerBound : ∀ value ∈ family, lower ≤ value) :
    ∃ infimum : Lp ℝ 2 measure,
      infimum =ᵐ[measure] (fun sample => ⨅ value : family, (value : Lp ℝ 2 measure) sample) ∧
      lower ≤ infimum ∧ IsGLB family infimum := by
  letI : Countable family := familyCountable.to_subtype
  letI : Nonempty family := familyNonempty.to_subtype
  obtain ⟨infimum, representative, lowerBoundInfimum, greatest⟩ :=
    exists_countable_lp2_infimum measure (fun value : family => (value : Lp ℝ 2 measure))
      lower lowerNonnegative (fun value => lowerBound value value.property)
  refine ⟨infimum, representative, lowerBoundInfimum, ?_⟩
  simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using greatest

private theorem lp2_norm_sq_eq_integral {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (value : Lp ℝ 2 measure) :
    ‖value‖ ^ 2 = ∫ sample, value sample ^ 2 ∂measure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem exists_antitone_lp2_limit {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (sequence : ℕ → Lp ℝ 2 measure)
    (antitone : Antitone sequence) (lower upper : Lp ℝ 2 measure)
    (lowerNonnegative : 0 ≤ lower)
    (bounds : ∀ index, lower ≤ sequence index ∧ sequence index ≤ upper) :
    ∃ limit : Lp ℝ 2 measure,
      Tendsto sequence atTop (𝓝 limit) ∧ lower ≤ limit ∧ limit ≤ upper ∧
      (∀ᵐ sample ∂measure, Tendsto (fun index => sequence index sample) atTop (𝓝 (limit sample))) ∧
      IsGLB (Set.range sequence) limit := by
  obtain ⟨limit, representative, lowerBoundLimit, greatest⟩ :=
    exists_countable_lp2_infimum measure sequence lower lowerNonnegative (fun index => (bounds index).1)
  have sequenceBounds : ∀ᵐ sample ∂measure, ∀ index,
      lower sample ≤ sequence index sample ∧ sequence index sample ≤ upper sample := by
    apply ae_all_iff.mpr
    intro index
    exact ((Lp.coeFn_le lower (sequence index)).mpr (bounds index).1).and
      ((Lp.coeFn_le (sequence index) upper).mpr (bounds index).2)
  have antitoneAe : ∀ᵐ sample ∂measure, Antitone (fun index => sequence index sample) := by
    have successive : ∀ᵐ sample ∂measure, ∀ index,
        sequence (index + 1) sample ≤ sequence index sample :=
      ae_all_iff.mpr (fun index => (Lp.coeFn_le (sequence (index + 1)) (sequence index)).mpr
        (antitone (Nat.le_succ index)))
    filter_upwards [successive] with sample inequalities
    exact antitone_nat_of_succ_le inequalities
  have pointwiseLimit : ∀ᵐ sample ∂measure,
      Tendsto (fun index => sequence index sample) atTop (𝓝 (limit sample)) := by
    filter_upwards [representative, sequenceBounds, antitoneAe] with sample equality sampleBounds sampleAntitone
    rw [equality]
    exact tendsto_atTop_ciInf sampleAntitone
      ⟨lower sample, by rintro _ ⟨index, rfl⟩; exact (sampleBounds index).1⟩
  have limitUpper : limit ≤ upper := (greatest.1 (Set.mem_range_self 0)).trans (bounds 0).2
  have limitNonnegative : 0 ≤ limit := lowerNonnegative.trans lowerBoundLimit
  have squaresTendsto : Tendsto
      (fun index => ∫ sample, (sequence index sample - limit sample) ^ 2 ∂measure)
      atTop (𝓝 0) := by
    have integralConvergence : Tendsto
        (fun index => ∫ sample, (sequence index sample - limit sample) ^ 2 ∂measure)
        atTop (𝓝 (∫ _sample : Sample, (0 : ℝ) ∂measure)) :=
      tendsto_integral_of_dominated_convergence
      (fun sample => upper sample ^ 2)
      (fun index => ((Lp.aestronglyMeasurable (sequence index)).sub (Lp.aestronglyMeasurable limit)).pow 2)
      (Lp.memLp upper).integrable_sq
      (show ∀ index, ∀ᵐ sample ∂measure, ‖(sequence index sample - limit sample) ^ 2‖ ≤ upper sample ^ 2 from by
        intro index
        filter_upwards [sequenceBounds,
          (Lp.coeFn_le limit (sequence index)).mpr (greatest.1 (Set.mem_range_self index)),
          (Lp.coeFn_nonneg limit).mpr limitNonnegative] with sample sampleBounds sampleLower sampleNonnegative
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have differenceNonnegative : 0 ≤ sequence index sample - limit sample := sub_nonneg.mpr sampleLower
        have differenceUpper : sequence index sample - limit sample ≤ upper sample :=
          (sub_le_self _ sampleNonnegative).trans (sampleBounds index).2
        nlinarith)
      (show ∀ᵐ sample ∂measure, Tendsto
          (fun index => (sequence index sample - limit sample) ^ 2) atTop (𝓝 (0 : ℝ)) from by
        filter_upwards [pointwiseLimit] with sample convergence
        simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
          (convergence.sub_const (limit sample)).pow 2)
    simpa only [integral_zero] using integralConvergence
  have normSquaresTendsto : Tendsto (fun index => ‖sequence index - limit‖ ^ 2) atTop (𝓝 0) := by
    convert squaresTendsto using 1
    funext index
    rw [lp2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (sequence index) limit] with sample equality
    rw [equality, Pi.sub_apply]
  have normsTendsto : Tendsto (fun index => ‖sequence index - limit‖) atTop (𝓝 0) := by
    have squareRootTendsto : Tendsto
        (fun index => Real.sqrt (‖sequence index - limit‖ ^ 2)) atTop (𝓝 (Real.sqrt (0 : ℝ))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp normSquaresTendsto
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using squareRootTendsto
  exact ⟨limit, tendsto_iff_norm_sub_tendsto_zero.mpr normsTendsto,
    lowerBoundLimit, limitUpper, pointwiseLimit, greatest⟩

end IGSIII.Probability
