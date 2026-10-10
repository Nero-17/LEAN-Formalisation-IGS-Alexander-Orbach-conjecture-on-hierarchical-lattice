import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Universality
noncomputable section
open Polynomial Filter
open scoped Topology

theorem polynomial_iteratedDeriv_eval (order : ℕ) (polynomial : Polynomial ℝ) :
    iteratedDeriv order polynomial.eval = (Polynomial.derivative^[order] polynomial).eval := by
  induction order generalizing polynomial with
  | zero => rfl
  | succ order ih =>
    rw [iteratedDeriv_succ']
    have hderivative : deriv polynomial.eval = polynomial.derivative.eval :=
      funext (fun point => polynomial.deriv)
    rw [hderivative, ih]
    rfl

theorem critical_first_jet_of_polynomial_renormalization
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization critical : ℝ)
    (hfixed : crossing.eval critical = critical) (hregular : DifferentiableAt ℝ density critical)
    (hequation : (fun p => mass * density p - density (crossing.eval p)) =ᶠ[𝓝 critical]
      (fun p => normalization * forcing.eval p)) :
    (mass - crossing.derivative.eval critical) * deriv density critical =
      normalization * forcing.derivative.eval critical := by
  have hnext : DifferentiableAt ℝ density (crossing.eval critical) := by
    simpa only [hfixed] using hregular
  have hleft := (hregular.hasDerivAt.const_mul mass).sub
    (hnext.hasDerivAt.comp critical (crossing.hasDerivAt critical))
  have hright := (forcing.hasDerivAt critical).const_mul normalization
  have hjet := (hleft.congr_of_eventuallyEq hequation.symm).unique hright
  rw [hfixed] at hjet
  nlinarith

theorem critical_second_jet_of_polynomial_renormalization
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization critical : ℝ)
    (hfixed : crossing.eval critical = critical) (hregular : ContDiffAt ℝ 2 density critical)
    (hequation : (fun p => mass * density p - density (crossing.eval p)) =ᶠ[𝓝 critical]
      (fun p => normalization * forcing.eval p)) :
    (mass - crossing.derivative.eval critical ^ 2) * iteratedDeriv 2 density critical =
      normalization * forcing.derivative.derivative.eval critical +
        crossing.derivative.derivative.eval critical * deriv density critical := by
  have hcrossing : ContDiffAt ℝ 2 crossing.eval critical :=
    ((AnalyticOnNhd.eval_polynomial crossing) critical (Set.mem_univ _)).contDiffAt
  have hnext : ContDiffAt ℝ 2 density (crossing.eval critical) := by simpa only [hfixed] using hregular
  have hjet := hequation.iteratedDeriv_eq 2
  change iteratedDeriv 2 ((fun p => mass * density p) - density ∘ crossing.eval) critical = _ at hjet
  rw [iteratedDeriv_sub (contDiffAt_const.mul hregular) (hnext.comp critical hcrossing),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_two hnext hcrossing,
    iteratedDeriv_const_mul_field] at hjet
  simp only [Polynomial.deriv, polynomial_iteratedDeriv_eval,
    Function.iterate_succ_apply, Function.iterate_zero_apply, hfixed] at hjet
  nlinarith

theorem critical_third_jet_of_polynomial_renormalization
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization critical : ℝ)
    (hfixed : crossing.eval critical = critical) (hregular : ContDiffAt ℝ 3 density critical)
    (hequation : (fun p => mass * density p - density (crossing.eval p)) =ᶠ[𝓝 critical]
      (fun p => normalization * forcing.eval p)) :
    (mass - crossing.derivative.eval critical ^ 3) * iteratedDeriv 3 density critical =
      normalization * forcing.derivative.derivative.derivative.eval critical +
        crossing.derivative.derivative.derivative.eval critical * deriv density critical +
          3 * crossing.derivative.eval critical * crossing.derivative.derivative.eval critical *
            iteratedDeriv 2 density critical := by
  have hcrossing : ContDiffAt ℝ 3 crossing.eval critical :=
    ((AnalyticOnNhd.eval_polynomial crossing) critical (Set.mem_univ _)).contDiffAt
  have hnext : ContDiffAt ℝ 3 density (crossing.eval critical) := by simpa only [hfixed] using hregular
  have hjet := hequation.iteratedDeriv_eq 3
  change iteratedDeriv 3 ((fun p => mass * density p) - density ∘ crossing.eval) critical = _ at hjet
  rw [iteratedDeriv_sub (contDiffAt_const.mul hregular) (hnext.comp critical hcrossing),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_three hnext hcrossing,
    iteratedDeriv_const_mul_field] at hjet
  simp only [Polynomial.deriv, polynomial_iteratedDeriv_eval,
    Function.iterate_succ_apply, Function.iterate_zero_apply, hfixed] at hjet
  nlinarith

end
end Universality
