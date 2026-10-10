import Universality.Percolation.InternalMassPositiveLocalLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

/-- The exact density of a positive rescaling of a real random variable. -/
theorem map_div_withDensity (radius : ℝ) (hradius : 0 < radius)
    (density : ℝ → ℝ) (hmeasurable : Measurable density) :
    (volume.withDensity (fun x => ENNReal.ofReal (density x))).map (fun x => x / radius) =
      volume.withDensity (fun x => ENNReal.ofReal (radius * density (radius * x))) := by
  have hdivide : Measurable (fun x : ℝ => x / radius) := measurable_id.div_const radius
  have hvolume : (volume : Measure ℝ).map (fun x => x / radius) =
      ENNReal.ofReal radius • volume := by
    simpa only [div_eq_mul_inv, inv_inv, abs_of_pos hradius] using
      (Real.map_volume_mul_right (inv_ne_zero hradius.ne'))
  apply Measure.ext_of_lintegral
  intro test htest
  have hcompose : Measurable (fun x : ℝ => test (x / radius)) := htest.comp hdivide
  have hscaled : Measurable (fun x : ℝ => ENNReal.ofReal (radius * density (radius * x))) :=
    (measurable_const.mul (hmeasurable.comp (measurable_const.mul measurable_id))).ennreal_ofReal
  rw [lintegral_map htest hdivide,
    lintegral_withDensity_eq_lintegral_mul _ hmeasurable.ennreal_ofReal hcompose,
    lintegral_withDensity_eq_lintegral_mul _ hscaled htest]
  have hproduct : Measurable (fun x : ℝ => ENNReal.ofReal (density (radius * x)) * test x) :=
    ((hmeasurable.comp (measurable_const.mul measurable_id)).ennreal_ofReal).mul htest
  calc
    (∫⁻ x : ℝ, ((fun x => ENNReal.ofReal (density x)) * (fun x => test (x / radius))) x) =
        ∫⁻ x : ℝ, ENNReal.ofReal (density (radius * (x / radius))) * test (x / radius) := by
      apply lintegral_congr
      intro x
      simp only [Pi.mul_apply]
      have hargument : radius * (x / radius) = x := by field_simp [hradius.ne']
      rw [hargument]
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (density (radius * x)) * test x
        ∂(volume.map (fun x : ℝ => x / radius)) := (lintegral_map hproduct hdivide).symm
    _ = ENNReal.ofReal radius * ∫⁻ x : ℝ, ENNReal.ofReal (density (radius * x)) * test x := by
      rw [hvolume, lintegral_smul_measure]
      rfl
    _ = ∫⁻ x : ℝ, ((fun x => ENNReal.ofReal (radius * density (radius * x))) * test) x := by
      rw [← lintegral_const_mul _ hproduct]
      apply lintegral_congr
      intro x
      simp only [Pi.mul_apply, ENNReal.ofReal_mul hradius.le, mul_assoc]

/-- This is a law identity for the very same random variable divided by radius. -/
theorem randomVariable_div_density {α : Type*} [MeasurableSpace α]
    (law : Measure α) (value : α → ℝ) (hvalue : AEMeasurable value law)
    (radius : ℝ) (hradius : 0 < radius) (density : ℝ → ℝ)
    (hmeasurable : Measurable density)
    (hlaw : law.map value = volume.withDensity (fun x => ENNReal.ofReal (density x))) :
    law.map (fun sample => value sample / radius) =
      volume.withDensity (fun x => ENNReal.ofReal (radius * density (radius * x))) := by
  have hdivide : Measurable (fun x : ℝ => x / radius) := measurable_id.div_const radius
  change law.map ((fun x : ℝ => x / radius) ∘ value) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hdivide.aemeasurable hvalue, hlaw]
  exact map_div_withDensity radius hradius density hmeasurable

end
end Universality
