import Universality.Probability.ContinuousDensitySupport
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

namespace Universality
noncomputable section
open MeasureTheory
open scoped ENNReal

theorem continuous_density_le_of_measure_le (first second : ℝ → ℝ)
    (hfirst : Continuous first) (hsecond : Continuous second)
    (hsecondNonneg : ∀ x, 0 ≤ second x)
    (hmeasure : volume.withDensity (fun x => ENNReal.ofReal (first x)) ≤
      volume.withDensity (fun x => ENNReal.ofReal (second x))) :
    ∀ x, first x ≤ second x := by
  have hae : (fun x => ENNReal.ofReal (first x)) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal (second x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hfirst.measurable.ennreal_ofReal
    intro region hregion _
    rw [← withDensity_apply _ hregion, ← withDensity_apply _ hregion]
    exact hmeasure region
  have hreal : ∀ᵐ x ∂volume, first x ≤ second x :=
    hae.mono (fun x hx => (ENNReal.ofReal_le_ofReal_iff (hsecondNonneg x)).mp hx)
  have hdense : Dense {x : ℝ | first x ≤ second x} := volume.dense_of_ae hreal
  have hclosed : IsClosed {x : ℝ | first x ≤ second x} := isClosed_le hfirst hsecond
  have hall : {x : ℝ | first x ≤ second x} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  intro x
  have := Set.mem_univ x
  rwa [← hall] at this

theorem continuous_density_weighted_le (firstLaw secondLaw : Measure ℝ)
    (first second : ℝ → ℝ) (weight : ℝ) (hweight : 0 ≤ weight)
    (hfirst : Continuous first) (hsecond : Continuous second)
    (hsecondNonneg : ∀ x, 0 ≤ second x)
    (hfirstLaw : firstLaw = volume.withDensity (fun x => ENNReal.ofReal (first x)))
    (hsecondLaw : secondLaw = volume.withDensity (fun x => ENNReal.ofReal (second x)))
    (hmeasure : ENNReal.ofReal weight • firstLaw ≤ secondLaw) :
    ∀ x, weight * first x ≤ second x := by
  apply continuous_density_le_of_measure_le (fun x => weight * first x) second
    (continuous_const.mul hfirst) hsecond hsecondNonneg
  have heq : volume.withDensity (fun x => ENNReal.ofReal (weight * first x)) =
      ENNReal.ofReal weight • firstLaw := by
    rw [hfirstLaw, ← withDensity_smul _ hfirst.measurable.ennreal_ofReal]
    congr 1
    funext x
    exact ENNReal.ofReal_mul hweight
  rwa [heq, ← hsecondLaw]

end
end Universality
