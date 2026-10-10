import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped ENNReal
variable {Sample : Type*} [ambient : MeasurableSpace Sample]
  (measure : Measure Sample) [IsFiniteMeasure measure]
  (information : MeasurableSpace Sample) (informationLe : information ≤ ambient)

def conditionalLp2 : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure := by
  letI : MeasurableSpace Sample := ambient
  exact (lpMeas ℝ ℝ information 2 measure).subtypeL.comp (condExpL2 ℝ ℝ informationLe)

theorem conditionalLp2_ae_eq_condExp (value : Lp ℝ 2 measure) :
    ⇑(conditionalLp2 (ambient := ambient) measure information informationLe value) =ᵐ[measure] measure[⇑value | information] := by
  letI : MeasurableSpace Sample := ambient
  have equality := (Lp.memLp value).condExpL2_ae_eq_condExp (𝕜 := ℝ) informationLe
  simpa only [Lp.toLp_coeFn, conditionalLp2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using equality

theorem conditionalLp2_norm_le (value : Lp ℝ 2 measure) :
    ‖conditionalLp2 (ambient := ambient) measure information informationLe value‖ ≤ ‖value‖ := by
  letI : MeasurableSpace Sample := ambient
  exact norm_condExpL2_coe_le informationLe value

theorem conditionalLp2_aestronglyMeasurable (value : Lp ℝ 2 measure) :
    AEStronglyMeasurable[information] (conditionalLp2 (ambient := ambient) measure information informationLe value) measure := by
  letI : MeasurableSpace Sample := ambient
  exact aestronglyMeasurable_condExpL2 informationLe value

theorem conditionalLp2_fixed (value : Lp ℝ 2 measure)
    (measurable : AEStronglyMeasurable[information] value measure) :
    conditionalLp2 (ambient := ambient) measure information informationLe value = value := by
  letI : MeasurableSpace Sample := ambient
  apply Lp.ext
  exact (conditionalLp2_ae_eq_condExp measure information informationLe value).trans
    (condExp_of_aestronglyMeasurable' informationLe measurable ((Lp.memLp value).integrable (by norm_num)))

theorem conditionalLp2_residual_le_approximation
    (value approximation : Lp ℝ 2 measure)
    (measurable : AEStronglyMeasurable[information] approximation measure) :
    ‖value-conditionalLp2 (ambient := ambient) measure information informationLe value‖ ≤ 2*‖value-approximation‖ := by
  letI : MeasurableSpace Sample := ambient
  have fixed := conditionalLp2_fixed measure information informationLe approximation measurable
  have bound : ‖approximation-conditionalLp2 (ambient := ambient) measure information informationLe value‖ ≤ ‖approximation-value‖ := by
    have inequality := conditionalLp2_norm_le measure information informationLe (approximation-value)
    rwa [map_sub, fixed] at inequality
  calc
    _ ≤ ‖value-approximation‖+‖approximation-conditionalLp2 (ambient := ambient) measure information informationLe value‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖value-approximation‖+‖approximation-value‖ := add_le_add le_rfl bound
    _ = _ := by rw [norm_sub_rev approximation value]; ring

theorem conditionalLp2_positive_part_residual_le (first second : Lp ℝ 2 measure) :
    ‖((first-second) ⊔ 0)-conditionalLp2 (ambient := ambient) measure information informationLe ((first-second) ⊔ 0)‖ ≤
      2*(‖first-conditionalLp2 (ambient := ambient) measure information informationLe first‖+
        ‖second-conditionalLp2 (ambient := ambient) measure information informationLe second‖) := by
  letI : MeasurableSpace Sample := ambient
  let approximation := (conditionalLp2 (ambient := ambient) measure information informationLe first-
    conditionalLp2 (ambient := ambient) measure information informationLe second) ⊔ 0
  have approximationMeasurable : AEStronglyMeasurable[information] approximation measure := by
    have differenceMeasurable := (conditionalLp2_aestronglyMeasurable measure information informationLe first).sub
      (conditionalLp2_aestronglyMeasurable measure information informationLe second)
    have measurable : AEStronglyMeasurable[information]
        (fun sample => max
          (conditionalLp2 (ambient := ambient) measure information informationLe first sample-
            conditionalLp2 (ambient := ambient) measure information informationLe second sample) 0) measure :=
      ⟨fun sample => max (differenceMeasurable.mk _ sample) 0,
        by
          letI : MeasurableSpace Sample := information
          exact differenceMeasurable.stronglyMeasurable_mk.sup stronglyMeasurable_const,
        differenceMeasurable.ae_eq_mk.mono (fun sample equality => by
          simp only [Pi.sub_apply] at equality
          exact congrArg (fun value : ℝ => max value 0) equality)⟩
    apply measurable.congr
    filter_upwards [Lp.coeFn_sup
        (conditionalLp2 (ambient := ambient) measure information informationLe first-
          conditionalLp2 (ambient := ambient) measure information informationLe second) 0,
      Lp.coeFn_sub (conditionalLp2 (ambient := ambient) measure information informationLe first)
        (conditionalLp2 (ambient := ambient) measure information informationLe second),
      Lp.coeFn_zero ℝ 2 measure] with sample supremum subtraction zero
    change _ = approximation sample
    rw [show approximation sample = _ from supremum, Pi.sup_apply, subtraction, Pi.sub_apply, zero]
    rfl
  have approximate := conditionalLp2_residual_le_approximation measure information informationLe
    ((first-second) ⊔ 0) approximation approximationMeasurable
  have contraction : ‖((first-second) ⊔ 0)-approximation‖ ≤
      ‖first-conditionalLp2 (ambient := ambient) measure information informationLe first‖+
        ‖second-conditionalLp2 (ambient := ambient) measure information informationLe second‖ := by
    apply (norm_sup_sub_sup_le_norm (first-second)
      (conditionalLp2 (ambient := ambient) measure information informationLe first-conditionalLp2 (ambient := ambient) measure information informationLe second) 0).trans
    have equality : first-second-(conditionalLp2 (ambient := ambient) measure information informationLe first-
        conditionalLp2 (ambient := ambient) measure information informationLe second) =
        (first-conditionalLp2 (ambient := ambient) measure information informationLe first)-(second-conditionalLp2 (ambient := ambient) measure information informationLe second) := by abel
    rw [equality]
    exact norm_sub_le _ _
  exact approximate.trans (mul_le_mul_of_nonneg_left contraction (by norm_num))

end
end IGSIII34.Probability


