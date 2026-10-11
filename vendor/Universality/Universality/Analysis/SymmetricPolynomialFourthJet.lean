import Universality.Analysis.PolynomialRenormalizationJets
import Universality.Percolation.ClusterNumberAlphaCriterion

namespace Universality
noncomputable section
open Polynomial Filter
open scoped Topology

theorem hasDerivAt_iteratedDeriv_of_contDiffAt (density : ℝ → ℝ) (critical : ℝ) (order : ℕ)
    (hregular : ContDiffAt ℝ (order + 1 : ℕ) density critical) :
    HasDerivAt (iteratedDeriv order density) (iteratedDeriv (order + 1) density critical) critical := by
  have hresponse : ContDiffAt ℝ 1 (iteratedDeriv order density) critical :=
    contDiffAt_iteratedDeriv_of_add density critical 1 order (by simpa only [Nat.add_comm] using hregular)
  simpa only [iteratedDeriv_succ] using (hresponse.differentiableAt (by norm_num)).hasDerivAt

theorem iteratedDeriv_comp_four_symmetric
    (density : ℝ → ℝ) (crossing : Polynomial ℝ) (critical : ℝ)
    (hregular : ContDiffAt ℝ 4 density critical) (hfixed : crossing.eval critical = critical)
    (hcrossSecond : crossing.derivative.derivative.eval critical = 0)
    (hcrossFourth : crossing.derivative.derivative.derivative.derivative.eval critical = 0)
    (hthird : iteratedDeriv 3 density critical = 0) :
    iteratedDeriv 4 (density ∘ crossing.eval) critical =
      iteratedDeriv 4 density critical * crossing.derivative.eval critical ^ 4 +
        4 * iteratedDeriv 2 density critical * crossing.derivative.eval critical *
          crossing.derivative.derivative.derivative.eval critical := by
  have hfirst : HasDerivAt (deriv density) (iteratedDeriv 2 density critical) (crossing.eval critical) := by
    rw [hfixed]
    simpa only [iteratedDeriv_one] using hasDerivAt_iteratedDeriv_of_contDiffAt density critical 1
      (hregular.of_le (by norm_num))
  have hsecond : HasDerivAt (iteratedDeriv 2 density) (iteratedDeriv 3 density critical) (crossing.eval critical) := by
    rw [hfixed]
    exact hasDerivAt_iteratedDeriv_of_contDiffAt density critical 2 (hregular.of_le (by norm_num))
  have hthirdDerivative : HasDerivAt (iteratedDeriv 3 density) (iteratedDeriv 4 density critical) (crossing.eval critical) := by
    rw [hfixed]
    exact hasDerivAt_iteratedDeriv_of_contDiffAt density critical 3 hregular
  have hterms := (((hthirdDerivative.comp critical (crossing.hasDerivAt critical)).mul
      ((crossing.derivative.hasDerivAt critical).pow 3)).add
    ((((hsecond.comp critical (crossing.hasDerivAt critical)).const_mul 3).mul
      (crossing.derivative.derivative.hasDerivAt critical)).mul
        (crossing.derivative.hasDerivAt critical))).add
    ((hfirst.comp critical (crossing.hasDerivAt critical)).mul
      (crossing.derivative.derivative.derivative.hasDerivAt critical))
  have hright : HasDerivAt
      (fun p => iteratedDeriv 3 density (crossing.eval p) * crossing.derivative.eval p ^ 3 +
        3 * iteratedDeriv 2 density (crossing.eval p) * crossing.derivative.derivative.eval p *
          crossing.derivative.eval p +
        deriv density (crossing.eval p) * crossing.derivative.derivative.derivative.eval p)
      (iteratedDeriv 4 density critical * crossing.derivative.eval critical ^ 4 +
        4 * iteratedDeriv 2 density critical * crossing.derivative.eval critical *
          crossing.derivative.derivative.derivative.eval critical) critical := by
    convert! hterms using 1
    dsimp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply]
    rw [hfixed, hcrossSecond, hcrossFourth, hthird]
    ring
  have hnextRegular : ∀ᶠ p in 𝓝 critical, ContDiffAt ℝ 4 density (crossing.eval p) := by
    have hnext : Tendsto crossing.eval (𝓝 critical) (𝓝 critical) := by
      simpa only [hfixed] using (crossing.hasDerivAt critical).continuousAt.tendsto
    exact hnext.eventually (hregular.eventually (by norm_num))
  have hlocal : iteratedDeriv 3 (density ∘ crossing.eval) =ᶠ[𝓝 critical]
      (fun p => iteratedDeriv 3 density (crossing.eval p) * crossing.derivative.eval p ^ 3 +
        3 * iteratedDeriv 2 density (crossing.eval p) * crossing.derivative.derivative.eval p *
          crossing.derivative.eval p +
        deriv density (crossing.eval p) * crossing.derivative.derivative.derivative.eval p) := by
    filter_upwards [hnextRegular] with p hp
    have hcrossing : ContDiffAt ℝ 3 crossing.eval p :=
      ((AnalyticOnNhd.eval_polynomial crossing) p (Set.mem_univ _)).contDiffAt
    simpa only [Polynomial.deriv, polynomial_iteratedDeriv_eval,
      Function.iterate_succ_apply, Function.iterate_zero_apply] using
        iteratedDeriv_comp_three (hp.of_le (by norm_num)) hcrossing
  have hactual := hright.congr_of_eventuallyEq hlocal
  simpa only [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ] using hactual.deriv

theorem critical_fourth_jet_of_symmetric_polynomial_renormalization
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization critical : ℝ)
    (hfixed : crossing.eval critical = critical) (hregular : ContDiffAt ℝ 4 density critical)
    (hcrossSecond : crossing.derivative.derivative.eval critical = 0)
    (hcrossFourth : crossing.derivative.derivative.derivative.derivative.eval critical = 0)
    (hthird : iteratedDeriv 3 density critical = 0)
    (hequation : (fun p => mass * density p - density (crossing.eval p)) =ᶠ[𝓝 critical]
      (fun p => normalization * forcing.eval p)) :
    (mass - crossing.derivative.eval critical ^ 4) * iteratedDeriv 4 density critical =
      normalization * forcing.derivative.derivative.derivative.derivative.eval critical +
        4 * iteratedDeriv 2 density critical * crossing.derivative.eval critical *
          crossing.derivative.derivative.derivative.eval critical := by
  have hcrossing : ContDiffAt ℝ 4 crossing.eval critical :=
    ((AnalyticOnNhd.eval_polynomial crossing) critical (Set.mem_univ _)).contDiffAt
  have hnext : ContDiffAt ℝ 4 density (crossing.eval critical) := by simpa only [hfixed] using hregular
  have hjet := hequation.iteratedDeriv_eq 4
  change iteratedDeriv 4 ((fun p => mass * density p) - density ∘ crossing.eval) critical = _ at hjet
  rw [iteratedDeriv_sub (contDiffAt_const.mul hregular) (hnext.comp critical hcrossing),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_four_symmetric density crossing critical
      hregular hfixed hcrossSecond hcrossFourth hthird, iteratedDeriv_const_mul_field] at hjet
  simp only [polynomial_iteratedDeriv_eval, Function.iterate_succ_apply, Function.iterate_zero_apply] at hjet
  nlinarith

end
end Universality
