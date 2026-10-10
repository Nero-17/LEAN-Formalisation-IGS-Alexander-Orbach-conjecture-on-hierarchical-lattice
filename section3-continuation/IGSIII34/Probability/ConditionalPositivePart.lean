import IGSIII34.Probability.ConditionalLp2
import IGSIII.Mass.BorelCantelli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem ae_positive_part_sub_condExp_tendsto_zero
    {Sample : Type*} [ambient : MeasurableSpace Sample]
    (measure : Measure Sample) [IsFiniteMeasure measure]
    (information : ℕ → MeasurableSpace Sample) (informationLe : ∀ depth, information depth ≤ ambient)
    (first second : ℕ → Lp ℝ 2 measure)
    (firstBound secondBound rate : ℝ) (firstBoundNonnegative : 0 ≤ firstBound)
    (secondBoundNonnegative : 0 ≤ secondBound) (rateNonnegative : 0 ≤ rate) (rateBelowOne : rate < 1)
    (firstResidual : ∀ depth,
      ‖first depth-conditionalLp2 measure (information depth) (informationLe depth) (first depth)‖ ≤ firstBound*rate^depth)
    (secondResidual : ∀ depth,
      ‖second depth-conditionalLp2 measure (information depth) (informationLe depth) (second depth)‖ ≤ secondBound*rate^depth) :
    ∀ᵐ sample ∂measure, Tendsto (fun depth => max (first depth sample-second depth sample) 0-
      measure[fun sample => max (first depth sample-second depth sample) 0 | information depth] sample)
      atTop (𝓝 0) := by
  let positivePart : ℕ → Lp ℝ 2 measure := fun depth => (first depth-second depth) ⊔ 0
  let error : ℕ → Lp ℝ 2 measure := fun depth => positivePart depth-
    conditionalLp2 measure (information depth) (informationLe depth) (positivePart depth)
  have errorBound (depth : ℕ) : ‖error depth‖ ≤ (2*(firstBound+secondBound))*rate^depth := by
    apply (conditionalLp2_positive_part_residual_le measure (information depth) (informationLe depth)
      (first depth) (second depth)).trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (firstResidual depth) (secondResidual depth))
      (by norm_num)).trans_eq (by ring)
  have convergence := IGSIII.Mass.ae_tendsto_zero_of_geometric_L2
    (fun depth sample => error depth sample) (fun depth => Lp.aestronglyMeasurable (error depth))
    (2*(firstBound+secondBound)) rate (mul_nonneg (by norm_num) (add_nonneg firstBoundNonnegative secondBoundNonnegative))
    rateNonnegative rateBelowOne (fun depth => by
      rw [show eLpNorm (error depth) 2 measure = ENNReal.ofReal ‖error depth‖ from by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]]
      exact ENNReal.ofReal_le_ofReal (errorBound depth))
  have positivePartEquality (depth : ℕ) : ⇑(positivePart depth) =ᵐ[measure]
      (fun sample => max (first depth sample-second depth sample) 0) := by
    filter_upwards [Lp.coeFn_sup (first depth-second depth) 0,
      Lp.coeFn_sub (first depth) (second depth), Lp.coeFn_zero ℝ 2 measure]
      with sample supremum subtraction zero
    change ((first depth-second depth) ⊔ 0) sample = _
    rw [supremum, Pi.sup_apply, subtraction, Pi.sub_apply, zero]
    rfl
  have errorEquality (depth : ℕ) : ⇑(error depth) =ᵐ[measure]
      (fun sample => max (first depth sample-second depth sample) 0-
        measure[fun sample => max (first depth sample-second depth sample) 0 | information depth] sample) := by
    have projected := (conditionalLp2_ae_eq_condExp measure (information depth) (informationLe depth) (positivePart depth)).trans
      (condExp_congr_ae (m := information depth) (positivePartEquality depth))
    filter_upwards [Lp.coeFn_sub (positivePart depth)
      (conditionalLp2 measure (information depth) (informationLe depth) (positivePart depth)),
      positivePartEquality depth, projected] with sample subtraction value conditional
    change (positivePart depth-conditionalLp2 measure (information depth) (informationLe depth) (positivePart depth)) sample = _
    rw [subtraction, Pi.sub_apply, value, conditional]
  filter_upwards [convergence, ae_all_iff.mpr errorEquality] with sample limit equalities
  simpa only [equalities] using limit

end
end IGSIII34.Probability

