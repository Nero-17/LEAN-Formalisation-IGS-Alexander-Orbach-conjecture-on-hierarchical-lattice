import Universality.Analysis.CompactEscapeLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Universality
noncomputable section
open Set Filter
open scoped Topology

theorem normalized_forcing_tendsto_zero {space : Type*} (filter : Filter space)
    (forcing deviation : space → ℝ) (order : ℝ) (horder : order < 1)
    (hbound : forcing =O[filter] deviation)
    (hdeviation : Tendsto deviation filter (𝓝 0))
    (hnonneg : ∀ᶠ point in filter, 0 ≤ deviation point) :
    Tendsto (fun point => forcing point / deviation point ^ order) filter (𝓝 0) := by
  have hpower : Tendsto (fun point => deviation point ^ (1 - order)) filter (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 - order)
      (Or.inr (sub_nonneg.mpr horder.le))).tendsto.comp hdeviation
    simpa only [Real.zero_rpow (sub_pos.mpr horder).ne', Function.comp_def] using h
  have hmajorant : (fun point => deviation point * (deviation point ^ order)⁻¹) =ᶠ[filter]
      (fun point => deviation point ^ (1 - order)) := by
    filter_upwards [hnonneg] with point hp
    rw [Real.rpow_one_sub' hp (sub_pos.mpr horder).ne', div_eq_mul_inv]
  have hscaled := hbound.mul (Asymptotics.isBigO_refl
    (fun point => (deviation point ^ order)⁻¹) filter)
  have h := hscaled.trans_tendsto (hpower.congr' hmajorant.symm)
  simpa only [div_eq_mul_inv] using h

theorem power_normalized_affine_equation {space : Type*}
    (iteration : space → space) (response coefficient forcing deviation secant : space → ℝ)
    (order : ℝ) (point : space) (hdeviation : 0 < deviation point) (hsecant : 0 < secant point)
    (hscale : deviation (iteration point) = deviation point * secant point)
    (hequation : response point = coefficient point * response (iteration point) + forcing point) :
    response point / deviation point ^ order =
      (coefficient point * secant point ^ order) *
        (response (iteration point) / deviation (iteration point) ^ order) +
          forcing point / deviation point ^ order := by
  rw [hscale, Real.mul_rpow hdeviation.le hsecant.le, hequation]
  field_simp [(Real.rpow_pos_of_pos hdeviation order).ne', (Real.rpow_pos_of_pos hsecant order).ne']

/-- The upper power barrier follows from compact escape. In particular no bound
on the normalized response near the center is assumed. -/
theorem continuous_power_normalized_response_of_compact_escape
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response coefficient forcing deviation secant : space → ℝ)
    (center : space) (outerRadius order : ℝ) (houterRadius : 0 < outerRadius) (horder : 0 < order)
    (hiteration : ContinuousAt iteration center) (hfixed : iteration center = center)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hdeviation : ContinuousOn deviation {center}ᶜ) (hzero : deviation center = 0)
    (hpositive : ∀ point ≠ center, 0 < deviation point)
    (hcoefficient : ContinuousAt coefficient center) (hsecant : ContinuousAt secant center)
    (hsecantPositive : ∀ point, 0 < secant point)
    (hforcing : ContinuousAt (fun point => forcing point / deviation point ^ order) center)
    (hcontract : |coefficient center * secant center ^ order| < 1)
    (hscale : ∀ point, deviation (iteration point) = deviation point * secant point)
    (hequation : ∀ᶠ point in 𝓝 center,
      response point = coefficient point * response (iteration point) + forcing point) :
    ContinuousAt (fun point => response point / deviation point ^ order) center := by
  apply continuousAt_of_compact_renormalization iteration
    (fun point => response point / deviation point ^ order)
    (fun point => coefficient point * secant point ^ order)
    (fun point => forcing point / deviation point ^ order) center outerRadius houterRadius
    hiteration hfixed hescape ?_
    (hcoefficient.mul (hsecant.rpow_const (Or.inl (hsecantPositive center).ne')))
    hforcing hcontract ?_
  · apply hresponse.div (hdeviation.rpow_const (fun point hp => Or.inr horder.le))
    intro point hp
    exact (Real.rpow_pos_of_pos (hpositive point hp) order).ne'
  · filter_upwards [hequation] with point heq
    by_cases hpoint : point = center
    · subst point
      simp only [hfixed, hzero, Real.zero_rpow horder.ne', div_zero, mul_zero, add_zero]
    · exact power_normalized_affine_equation iteration response coefficient forcing deviation secant
        order point (hpositive point hpoint) (hsecantPositive point) (hscale point) heq

/-- The lower power barrier uses positivity only on the exit set, transported
backward by a coefficient greater than one. -/
theorem positive_lower_power_barrier_of_compact_escape
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response coefficient forcing deviation secant : space → ℝ)
    (center : space) (outerRadius order : ℝ) (houterRadius : 0 < outerRadius) (horder : 0 < order)
    (hfixed : iteration center = center)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hresponsePositive : ∀ point ≠ center, 0 < response point)
    (hresponseCenter : 0 ≤ response center)
    (hdeviation : ContinuousOn deviation {center}ᶜ) (hzero : deviation center = 0)
    (hpositive : ∀ point ≠ center, 0 < deviation point)
    (hsecantPositive : ∀ point, 0 < secant point)
    (hcoefficient : ∀ᶠ point in 𝓝 center, 1 ≤ coefficient point * secant point ^ order)
    (hforcing : ∀ᶠ point in 𝓝 center, 0 ≤ forcing point)
    (hscale : ∀ point, deviation (iteration point) = deviation point * secant point)
    (hequation : ∀ᶠ point in 𝓝 center,
      response point = coefficient point * response (iteration point) + forcing point) :
    ∃ bound > 0, ∀ point ≠ center, bound * deviation point ^ order ≤ response point := by
  have hresponseNonneg (point : space) : 0 ≤ response point := by
    by_cases hp : point = center
    · simpa only [hp] using hresponseCenter
    · exact (hresponsePositive point hp).le
  have hdeviationNonneg (point : space) : 0 ≤ deviation point := by
    by_cases hp : point = center
    · simp only [hp, hzero, le_refl]
    · exact (hpositive point hp).le
  obtain ⟨bound, hbound, hboundResponse⟩ := positive_lower_bound_of_compact_escape iteration
    (fun point => response point / deviation point ^ order) center outerRadius houterRadius hescape
    (hresponse.div (hdeviation.rpow_const (fun point hp => Or.inr horder.le))
      (fun point hp => (Real.rpow_pos_of_pos (hpositive point hp) order).ne'))
    (fun point hp => div_pos (hresponsePositive point hp) (Real.rpow_pos_of_pos (hpositive point hp) order))
    (by
      filter_upwards [hequation, hcoefficient, hforcing] with point heq hcoef hforce
      by_cases hpoint : point = center
      · subst point
        simp only [hfixed, le_refl]
      · rw [power_normalized_affine_equation iteration response coefficient forcing deviation secant
          order point (hpositive point hpoint) (hsecantPositive point) (hscale point) heq]
        have hnext : 0 ≤ response (iteration point) / deviation (iteration point) ^ order :=
          div_nonneg (hresponseNonneg _) (Real.rpow_nonneg (hdeviationNonneg _) _)
        have hscaled := mul_le_mul_of_nonneg_right hcoef hnext
        have hforce := div_nonneg hforce (Real.rpow_nonneg (hdeviationNonneg point) order)
        nlinarith)
  refine ⟨bound, hbound, fun point hp => ?_⟩
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (hpositive point hp) order)).mp (hboundResponse point hp)

end
end Universality
