import Universality.Analysis.DerivativeRenormalization
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace Universality
noncomputable section
open Filter Set
open scoped Topology ContDiff

/-- Finite-order regularity at a repelling point follows by differentiating
its scalar functional equation. At each step the coefficient gains one factor
of the expansion derivative, giving the exact threshold in the hypothesis. -/
theorem contDiffAt_of_repelling_renormalization
    (order : ℕ) (iteration : ℝ → ℝ) (lower upper center : ℝ)
    (hcenterLower : lower < center) (hcenterUpper : center < upper)
    (hmaps : MapsTo iteration (Icc lower upper) (Icc lower upper))
    (hiteration : AnalyticAt ℝ iteration center) (hfixed : iteration center = center)
    (hrepelling : 1 < deriv iteration center)
    (hne : ∀ point ∈ Icc lower upper, point ≠ center → iteration point ≠ center)
    (hescape : ∃ radius : ℝ, 0 < radius ∧ ∀ point ∈ Icc lower upper,
      point ≠ center → ∃ depth : ℕ, radius ≤ |iteration^[depth] point - center|)
    (response coefficient forcing : ℝ → ℝ)
    (hresponse : ContinuousAt response center)
    (hanalytic : ∀ point ∈ Icc lower upper, point ≠ center → AnalyticAt ℝ response point)
    (hcoefficient : AnalyticAt ℝ coefficient center)
    (hforcing : ContDiffAt ℝ order forcing center)
    (hequation : response =ᶠ[𝓝 center]
      (fun point => coefficient point * response (iteration point) + forcing point))
    (hcontract : |coefficient center| * deriv iteration center ^ order < 1) :
    ContDiffAt ℝ order response center := by
  induction order generalizing response coefficient forcing with
  | zero =>
    simp only [Nat.cast_zero, contDiffAt_zero]
    refine ⟨Ioo lower upper, Ioo_mem_nhds hcenterLower hcenterUpper, ?_⟩
    intro point hp
    by_cases hpoint : point = center
    · subst point
      exact hresponse.continuousWithinAt
    exact (hanalytic point ⟨hp.1.le, hp.2.le⟩ hpoint).continuousAt.continuousWithinAt
  | succ order ih =>
    have hpositive : 0 < deriv iteration center := zero_lt_one.trans hrepelling
    have hpreviousContract : |coefficient center| * deriv iteration center ^ order < 1 :=
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hrepelling.le (Nat.le_succ order)) (abs_nonneg _)).trans_lt hcontract
    have hpreviousForcing : ContDiffAt ℝ order forcing center := hforcing.of_le (by exact_mod_cast Nat.le_succ order)
    have hprevious := ih response coefficient forcing hresponse hanalytic hcoefficient
      hpreviousForcing hequation hpreviousContract
    let nextCoefficient (point : ℝ) := coefficient point * deriv iteration point
    let nextForcing (point : ℝ) := deriv coefficient point * response (iteration point) + deriv forcing point
    have hnextCoefficient : AnalyticAt ℝ nextCoefficient center := hcoefficient.mul hiteration.deriv
    have hpreviousAtNext : ContDiffAt ℝ order response (iteration center) := by
      simpa only [hfixed] using hprevious
    have hcoefficientDerivative : ContDiffAt ℝ order (deriv coefficient) center := hcoefficient.deriv.contDiffAt
    have hnextForcing : ContDiffAt ℝ order nextForcing center :=
      (hcoefficientDerivative.mul
        (hpreviousAtNext.comp center hiteration.contDiffAt)).add
          (hforcing.derivWithin (by simp))
    have hnextContract : |nextCoefficient center| * deriv iteration center ^ order < 1 := by
      dsimp [nextCoefficient]
      rw [abs_mul, abs_of_pos hpositive]
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hcontract
    have hfirstContract : |nextCoefficient center| < 1 := by
      have hpow : 1 ≤ deriv iteration center ^ order := one_le_pow₀ hrepelling.le
      exact (le_mul_of_one_le_right (abs_nonneg _) hpow).trans_lt hnextContract
    have hlocal : ∀ᶠ point in 𝓝 center,
        point ∈ Ioo lower upper ∧ AnalyticAt ℝ iteration point ∧
        AnalyticAt ℝ coefficient point ∧ ContDiffAt ℝ (order + 1) forcing point ∧
        response =ᶠ[𝓝 point] (fun x => coefficient x * response (iteration x) + forcing x) := by
      filter_upwards [Ioo_mem_nhds hcenterLower hcenterUpper, hiteration.eventually_analyticAt,
        hcoefficient.eventually_analyticAt, hforcing.eventually (by simp), hequation.eventuallyEq_nhds]
        with point hp hi ha hb heq
      exact ⟨hp, hi, ha, hb, heq⟩
    have hpunctured : ∀ᶠ point in 𝓝 center, point ≠ center → deriv response point =
        nextCoefficient point * deriv response (iteration point) + nextForcing point := by
      filter_upwards [hlocal] with point hp hpoint
      have hclosed : point ∈ Icc lower upper := ⟨hp.1.1.le, hp.1.2.le⟩
      exact deriv_eq_of_renormalization response iteration coefficient forcing point
        (hanalytic point hclosed hpoint).differentiableAt
        (hanalytic (iteration point) (hmaps hclosed) (hne point hclosed hpoint)).differentiableAt
        hp.2.1.differentiableAt hp.2.2.1.differentiableAt
        (hp.2.2.2.1.differentiableAt (by simp)) hp.2.2.2.2
    have hfirst := derivative_continuous_of_renormalization response iteration nextCoefficient nextForcing
      lower upper center hcenterLower hcenterUpper hmaps hiteration.continuousAt hfixed hne hescape
      hresponse hanalytic hnextCoefficient.continuousAt hnextForcing.continuousAt hfirstContract hpunctured
    have hresponseDiff (point : ℝ) (hp : point ∈ Icc lower upper) : DifferentiableAt ℝ response point := by
      by_cases hpoint : point = center
      · subst point
        exact hfirst.1.differentiableAt
      exact (hanalytic point hp hpoint).differentiableAt
    have hnextEquation : deriv response =ᶠ[𝓝 center]
        (fun point => nextCoefficient point * deriv response (iteration point) + nextForcing point) := by
      filter_upwards [hlocal] with point hp
      have hclosed : point ∈ Icc lower upper := ⟨hp.1.1.le, hp.1.2.le⟩
      exact deriv_eq_of_renormalization response iteration coefficient forcing point
        (hresponseDiff point hclosed) (hresponseDiff (iteration point) (hmaps hclosed))
        hp.2.1.differentiableAt hp.2.2.1.differentiableAt
        (hp.2.2.2.1.differentiableAt (by simp)) hp.2.2.2.2
    have hnextRegular := ih (deriv response) nextCoefficient nextForcing hfirst.2
      (fun point hp hpoint => (hanalytic point hp hpoint).deriv)
      hnextCoefficient hnextForcing hnextEquation hnextContract
    apply contDiffAt_succ_of_deriv response center order ?_ hnextRegular
    filter_upwards [Ioo_mem_nhds hcenterLower hcenterUpper] with point hp
    exact hresponseDiff point ⟨hp.1.le, hp.2.le⟩

end
end Universality

