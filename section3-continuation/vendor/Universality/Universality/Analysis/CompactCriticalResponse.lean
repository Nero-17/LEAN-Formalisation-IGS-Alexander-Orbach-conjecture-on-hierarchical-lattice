import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Universality.Analysis.CompactEscapeUpperBound
import Universality.Analysis.AffineCriticalCorrections

namespace Universality
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology

theorem bounded_positive_normalized_response_of_compact_escape
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response coefficient forcing distance : space → ℝ)
    (center : space) (outerRadius expansion rate bound power : ℝ)
    (houterRadius : 0 < outerRadius) (hexpansion : 1 < expansion)
    (hrate : 0 < rate) (hbound : 0 ≤ bound) (hpower : 0 < power)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hresponseNonnegative : ∀ point, 0 ≤ response point)
    (hresponsePositive : ∀ point ≠ center, 0 < response point)
    (hdistance : ContinuousOn distance {center}ᶜ)
    (hdistanceNonnegative : ∀ point, 0 ≤ distance point)
    (hequation : ∀ᶠ point in 𝓝 center,
      response point = coefficient point * response (iteration point) + forcing point)
    (hcoefficient : ∀ᶠ point in 𝓝 center, coefficient point ≤ 1 ∧
      1 ≤ Real.exp (rate * distance point) * coefficient point)
    (hgrowth : ∀ᶠ point in 𝓝 center, expansion * distance point ≤ distance (iteration point))
    (hforcing : ∀ᶠ point in 𝓝 center, 0 ≤ forcing point ∧ forcing point ≤ bound * distance point ^ power) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ point ≠ center,
      lower ≤ response point ∧ response point ≤ upper := by
  have hpowerExpansion : 1 < expansion ^ power := Real.one_lt_rpow hexpansion hpower
  have hcorrectionNonnegative : 0 ≤ bound / (expansion ^ power - 1) :=
    div_nonneg hbound (sub_pos.mpr hpowerExpansion).le
  obtain ⟨upper, hupper, hupperBound⟩ := nonnegative_upper_bound_of_compact_escape iteration
    (fun point => response point + (bound / (expansion ^ power - 1)) * distance point ^ power)
    center outerRadius houterRadius hescape
    (hresponse.add (continuousOn_const.mul (hdistance.rpow_const (fun _ _ => Or.inr hpower.le))))
    (fun point => add_nonneg (hresponseNonnegative point)
      (mul_nonneg hcorrectionNonnegative (Real.rpow_nonneg (hdistanceNonnegative point) power))) (by
      filter_upwards [hequation, hcoefficient, hgrowth, hforcing] with point he hc hg hf
      exact affine_additive_power_correction _ _ _ _ _ _ expansion bound power
        (hresponseNonnegative _) hc.1 he (hdistanceNonnegative point) hexpansion hg hbound hpower hf.2)
  obtain ⟨lower, hlower, hlowerBound⟩ := positive_lower_bound_of_compact_escape iteration
    (fun point => Real.exp (-(rate / (expansion - 1)) * distance point) * response point)
    center outerRadius houterRadius hescape
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hdistance)).mul hresponse)
    (fun point hp => mul_pos (Real.exp_pos _) (hresponsePositive point hp)) (by
      filter_upwards [hequation, hcoefficient, hgrowth, hforcing] with point he hc hg hf
      exact affine_exponential_correction _ _ _ _ _ _ expansion rate
        (hresponseNonnegative _) hf.1 he hexpansion hrate hg hc.2)
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro point hp
  constructor
  · apply (hlowerBound point hp).trans
    have hnegative : -(rate / (expansion - 1)) * distance point ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_pos hrate (sub_pos.mpr hexpansion)).le)
        (hdistanceNonnegative point)
    have he := Real.exp_le_one_iff.mpr hnegative
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (hresponseNonnegative point)
  · exact (le_add_of_nonneg_right (mul_nonneg hcorrectionNonnegative
      (Real.rpow_nonneg (hdistanceNonnegative point) power))).trans (hupperBound point hp)

end
end Universality
