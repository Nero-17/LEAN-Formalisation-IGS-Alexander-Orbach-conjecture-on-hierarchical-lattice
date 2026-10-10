import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory
open scoped ENNReal

theorem lp2_mean_continuous {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsFiniteMeasure measure] :
    Continuous (fun value : Lp ℝ 2 measure => ∫ sample, value sample ∂measure) := by
  let constantOne : Lp ℝ 2 measure := (memLp_const (μ := measure) (p := 2) (1 : ℝ)).toLp (fun _ => 1)
  have constantOneRepresentative : constantOne =ᵐ[measure] (fun _ => (1 : ℝ)) := MemLp.coeFn_toLp _
  have equality : (fun value : Lp ℝ 2 measure => ∫ sample, value sample ∂measure) =
      (fun value => inner ℝ constantOne value) := by
    funext value
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [constantOneRepresentative] with sample sampleEquality
    rw [sampleEquality]
    change value sample = value sample * 1
    exact (mul_one _).symm
  rw [equality]
  exact continuous_const.inner continuous_id

theorem lp2_mean_mono {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsFiniteMeasure measure]
    {first second : Lp ℝ 2 measure} (comparison : first ≤ second) :
    (∫ sample, first sample ∂measure) ≤ ∫ sample, second sample ∂measure :=
  integral_mono_ae (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp first))
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp second))
    ((Lp.coeFn_le first second).mpr comparison)

end IGSIII.Probability
