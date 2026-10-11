import Universality.Analysis.CompactRenormalizationResponse
import Universality.Analysis.PuncturedDerivativeExtension
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Piecewise

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

theorem deriv_eq_of_renormalization (response iteration coefficient forcing : ℝ → ℝ)
    (point : ℝ) (hresponse : DifferentiableAt ℝ response point)
    (hnext : DifferentiableAt ℝ response (iteration point))
    (hiteration : DifferentiableAt ℝ iteration point)
    (hcoefficient : DifferentiableAt ℝ coefficient point)
    (hforcing : DifferentiableAt ℝ forcing point)
    (hequation : response =ᶠ[𝓝 point]
      (fun x => coefficient x * response (iteration x) + forcing x)) :
    deriv response point = (coefficient point * deriv iteration point) *
        deriv response (iteration point) +
      (deriv coefficient point * response (iteration point) + deriv forcing point) := by
  have hright := ((hcoefficient.hasDerivAt.mul (hnext.hasDerivAt.comp point
    hiteration.hasDerivAt)).add hforcing.hasDerivAt).congr_of_eventuallyEq hequation
  have heq := hresponse.hasDerivAt.unique hright
  rw [heq]
  simp only [Function.comp_apply]
  ring

/-- A punctured derivative obeying a contractive renormalization extends to a
continuous genuine derivative at the critical point. The only assumptions on
the original response there are continuity and its punctured equation. -/
theorem derivative_continuous_of_renormalization
    (response iteration coefficient forcing : ℝ → ℝ) (lower upper center : ℝ)
    (hcenterLower : lower < center) (hcenterUpper : center < upper)
    (hmaps : MapsTo iteration (Icc lower upper) (Icc lower upper))
    (hiteration : ContinuousAt iteration center) (hfixed : iteration center = center)
    (hne : ∀ point ∈ Icc lower upper, point ≠ center → iteration point ≠ center)
    (hescape : ∃ radius : ℝ, 0 < radius ∧ ∀ point ∈ Icc lower upper,
      point ≠ center → ∃ depth : ℕ, radius ≤ |iteration^[depth] point - center|)
    (hresponse : ContinuousAt response center)
    (hanalytic : ∀ point ∈ Icc lower upper, point ≠ center → AnalyticAt ℝ response point)
    (hcoefficient : ContinuousAt coefficient center) (hforcing : ContinuousAt forcing center)
    (hcontract : |coefficient center| < 1)
    (hequation : ∀ᶠ point in 𝓝 center, point ≠ center →
      deriv response point = coefficient point * deriv response (iteration point) + forcing point) :
    HasDerivAt response (forcing center / (1 - coefficient center)) center ∧
      ContinuousAt (deriv response) center := by
  let unitCenter : Icc lower upper := ⟨center, hcenterLower.le, hcenterUpper.le⟩
  let unitIteration (point : Icc lower upper) : Icc lower upper :=
    ⟨iteration point.val, hmaps point.property⟩
  have hiterateVal (depth : ℕ) (point : Icc lower upper) :
      (unitIteration^[depth] point).val = iteration^[depth] point.val := by
    induction depth generalizing point with
    | zero => rfl
    | succ depth ih =>
      simpa only [Function.iterate_succ_apply] using ih (unitIteration point)
  let value := forcing center / (1 - coefficient center)
  have hgap : 1 - coefficient center ≠ 0 := by
    have := le_abs_self (coefficient center)
    linarith
  have hvalue : value = coefficient center * value + forcing center := by
    have heq : value * (1 - coefficient center) = forcing center := (eq_div_iff hgap).mp rfl
    nlinarith
  let patched := Function.update (deriv response) center value
  have hpatchedCenter : patched center = value := Function.update_self ..
  obtain ⟨radius, hradius, hexit⟩ := hescape
  have hunitContinuous : ContinuousAt unitIteration unitCenter :=
    (hiteration.comp (continuousAt_subtype_val (x := unitCenter))).codRestrict _
  have hcontinuous : ContinuousAt (fun point : Icc lower upper => patched point.val) unitCenter := by
    apply continuousAt_of_compact_renormalization unitIteration
      (fun point => patched point.val) (fun point => coefficient point.val)
      (fun point => forcing point.val) unitCenter radius hradius hunitContinuous (Subtype.ext hfixed)
    · intro point hp
      obtain ⟨depth, hdepth⟩ := hexit point.val point.property
        (fun heq => hp (Subtype.ext heq))
      exact ⟨depth, by simpa only [Subtype.dist_eq, Real.dist_eq, hiterateVal] using hdepth⟩
    · intro point hp
      have hpoint : point.val ≠ center := fun heq => hp (Set.mem_singleton_iff.mpr (Subtype.ext heq))
      exact (((continuousAt_update_of_ne hpoint).mpr
        (hanalytic point.val point.property hpoint).deriv.continuousAt).comp
          (continuousAt_subtype_val (x := point))).continuousWithinAt
    · exact hcoefficient.comp (continuousAt_subtype_val (x := unitCenter))
    · exact hforcing.comp (continuousAt_subtype_val (x := unitCenter))
    · exact hcontract
    · have hlocal := (continuousAt_subtype_val (x := unitCenter)).eventually hequation
      filter_upwards [hlocal] with point hp
      change patched point.val = coefficient point.val * patched (iteration point.val) + forcing point.val
      by_cases hpoint : point.val = center
      · simpa only [hpoint, hfixed, hpatchedCenter] using hvalue
      simp only [patched, Function.update_of_ne hpoint,
        Function.update_of_ne (hne point.val point.property hpoint)]
      exact hp hpoint
  have hcontinuousReal : ContinuousAt patched center :=
    ((continuousWithinAt_iff_continuousAt_restrict patched unitCenter.property).mpr
      hcontinuous).continuousAt (Icc_mem_nhds hcenterLower hcenterUpper)
  have hlimit : Tendsto (deriv response) (𝓝[≠] center) (𝓝 value) :=
    continuousAt_update_same.mp hcontinuousReal
  have hhasDeriv : HasDerivAt response value center := by
    apply hasDerivAt_of_punctured_derivative_limit response (deriv response) center value hresponse ?_ hlimit
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hcenterLower hcenterUpper), self_mem_nhdsWithin]
      with point hp hpoint
    exact (hanalytic point ⟨hp.1.le, hp.2.le⟩ hpoint).differentiableAt.hasDerivAt
  refine ⟨hhasDeriv, ?_⟩
  have heq : patched = deriv response := by
    funext point
    by_cases hp : point = center
    · subst point
      exact hpatchedCenter.trans hhasDeriv.deriv.symm
    exact Function.update_of_ne hp ..
  rwa [heq] at hcontinuousReal

end
end Universality

