import Universality.Probability.IndependentSupport
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos

namespace Universality
noncomputable section
open MeasureTheory
open scoped Topology ENNReal

theorem continuous_density_zero_on_open_null (measure : Measure ℝ) (density : ℝ → ℝ)
    (hcontinuous : Continuous density) (hnonnegative : ∀ x, 0 ≤ density x)
    (hdensity : measure = volume.withDensity (fun x => ENNReal.ofReal (density x)))
    (region : Set ℝ) (hopen : IsOpen region) (hnull : measure region = 0)
    (x : ℝ) (hx : x ∈ region) : density x = 0 := by
  by_contra hne
  have hpositive : 0 < density x := lt_of_le_of_ne (hnonnegative x) (Ne.symm hne)
  have hzero : volume ({y : ℝ | ENNReal.ofReal (density y) ≠ 0} ∩ region) = 0 := by
    apply (withDensity_apply_eq_zero hcontinuous.measurable.ennreal_ofReal).mp
    rwa [← hdensity]
  have hsubset : region ∩ {y : ℝ | 0 < density y} ⊆
      {y : ℝ | ENNReal.ofReal (density y) ≠ 0} ∩ region := by
    intro y hy
    exact ⟨(ENNReal.ofReal_pos.mpr hy.2).ne', hy.1⟩
  have hpos : 0 < volume (region ∩ {y : ℝ | 0 < density y}) :=
    (hopen.inter (isOpen_lt continuous_const hcontinuous)).measure_pos volume ⟨x, hx, hpositive⟩
  exact hpos.ne' (measure_mono_null hsubset hzero)

theorem continuous_density_zero_outside_support (measure : Measure ℝ) (density : ℝ → ℝ)
    (hcontinuous : Continuous density) (hnonnegative : ∀ x, 0 ≤ density x)
    (hdensity : measure = volume.withDensity (fun x => ENNReal.ofReal (density x)))
    (x : ℝ) (hx : x ∉ measure.support) : density x = 0 :=
  continuous_density_zero_on_open_null measure density hcontinuous hnonnegative hdensity
    measure.supportᶜ measure.isClosed_support.isOpen_compl measure.measure_compl_support x hx

theorem continuous_density_zero_of_negative (measure : Measure ℝ) (density : ℝ → ℝ)
    (hcontinuous : Continuous density) (hnonnegative : ∀ x, 0 ≤ density x)
    (hdensity : measure = volume.withDensity (fun x => ENNReal.ofReal (density x)))
    (hsupport : measure.support ⊆ Set.Ici 0) (x : ℝ) (hx : x < 0) : density x = 0 := by
  apply continuous_density_zero_outside_support measure density hcontinuous hnonnegative hdensity x
  intro hmem
  exact (not_le_of_gt hx) (hsupport hmem)

theorem exists_positive_density_in_open (measure : Measure ℝ) (density : ℝ → ℝ)
    (hcontinuous : Continuous density)
    (hdensity : measure = volume.withDensity (fun x => ENNReal.ofReal (density x)))
    (region : Set ℝ) (hpositive : 0 < measure region) :
    ∃ x ∈ region, 0 < density x := by
  by_contra hnone
  push_neg at hnone
  have hempty : {y : ℝ | ENNReal.ofReal (density y) ≠ 0} ∩ region = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hy.1 (ENNReal.ofReal_eq_zero.mpr (hnone y hy.2))
  have hzero : measure region = 0 := by
    rw [hdensity, withDensity_apply_eq_zero hcontinuous.measurable.ennreal_ofReal, hempty]
    exact measure_empty
  exact hpositive.ne' hzero

theorem integral_positive_of_support_point (measure : Measure ℝ) (function : ℝ → ℝ)
    (hcontinuous : Continuous function) (hnonnegative : ∀ x, 0 ≤ function x)
    (hintegrable : Integrable function measure)
    (point : ℝ) (hpoint : point ∈ measure.support) (hpositive : 0 < function point) :
    0 < ∫ x, function x ∂measure := by
  apply (integral_pos_iff_support_of_nonneg hnonnegative hintegrable).mpr
  have hpos : 0 < measure {x : ℝ | 0 < function x} := by
    rw [Measure.support_eq_forall_isOpen] at hpoint
    exact hpoint _ hpositive (isOpen_lt continuous_const hcontinuous)
  apply hpos.trans_le
  apply measure_mono
  intro x hx
  exact hx.ne'

theorem convolution_positive_of_full_positive_support
    (measure other : Measure ℝ) (density : ℝ → ℝ)
    (hcontinuous : Continuous density) (hnonnegative : ∀ x, 0 ≤ density x)
    (hdensity : measure = volume.withDensity (fun x => ENNReal.ofReal (density x)))
    (hsupport : ∀ x : ℝ, 0 < x → x ∈ measure.support)
    (hother : ∀ x : ℝ, 0 < x → x ∈ other.support)
    (x : ℝ) (hx : 0 < x) (hintegrable : Integrable (fun y => density (x - y)) other) :
    0 < ∫ y, density (x - y) ∂other := by
  have hregion : 0 < measure (Set.Ioo 0 x) := by
    have hpoint := hsupport (x / 2) (by linarith)
    rw [Measure.support_eq_forall_isOpen] at hpoint
    exact hpoint _ (show x / 2 ∈ Set.Ioo 0 x by constructor <;> linarith) isOpen_Ioo
  obtain ⟨point, hpoint, hpositive⟩ :=
    exists_positive_density_in_open measure density hcontinuous hdensity (Set.Ioo 0 x) hregion
  apply integral_positive_of_support_point other (fun y => density (x - y))
    (hcontinuous.comp (continuous_const.sub continuous_id)) (fun y => hnonnegative _) hintegrable
    (x - point) (hother (x - point) (sub_pos.mpr hpoint.2))
  simpa only [sub_sub_cancel] using hpositive

end
end Universality
