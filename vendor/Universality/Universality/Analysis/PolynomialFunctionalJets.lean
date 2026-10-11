import Universality.Analysis.PolynomialRenormalizationJets
import Universality.Percolation.ClusterNumberUnitRegularity

namespace Universality
noncomputable section
open Filter Set Polynomial
open scoped Topology

/-- Agreement on the physical interval determines all finite derivatives at
its endpoints as well, because both sides have the asserted neighborhood
regularity. -/
theorem closed_polynomial_functional_jet
    (order : ℕ) (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization : ℝ)
    (hmaps : MapsTo crossing.eval (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hregular : ∀ p ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ order density p)
    (hequation : EqOn (fun p => mass * density p - density (crossing.eval p))
      (fun p => normalization * forcing.eval p) (Icc (0 : ℝ) 1)) :
    ∀ p ∈ Icc (0 : ℝ) 1,
      iteratedDeriv order (fun q => mass * density q - density (crossing.eval q)) p =
        normalization * (Polynomial.derivative^[order] forcing).eval p := by
  have hleftContinuous : ContinuousOn
      (iteratedDeriv order (fun q => mass * density q - density (crossing.eval q))) (Icc (0 : ℝ) 1) := by
    intro p hp
    have hcrossing : ContDiffAt ℝ order crossing.eval p :=
      ((AnalyticOnNhd.eval_polynomial crossing) p (mem_univ _)).contDiffAt
    have hleftRegular : ContDiffAt ℝ order
        (fun q => mass * density q - density (crossing.eval q)) p :=
      (contDiffAt_const.mul (hregular p hp)).sub ((hregular _ (hmaps hp)).comp p hcrossing)
    have hjetRegular := contDiffAt_iteratedDeriv_of_add
      (fun q => mass * density q - density (crossing.eval q)) p 0 order
        (by simpa only [zero_add] using hleftRegular)
    exact hjetRegular.continuousAt.continuousWithinAt
  have hinterior : EqOn
      (iteratedDeriv order (fun q => mass * density q - density (crossing.eval q)))
      (fun p => normalization * (Polynomial.derivative^[order] forcing).eval p) (Ioo (0 : ℝ) 1) := by
    intro p hp
    have hlocal : (fun q => mass * density q - density (crossing.eval q)) =ᶠ[𝓝 p]
        (fun q => normalization * forcing.eval q) := by
      filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
      exact hequation ⟨hq.1.le, hq.2.le⟩
    have hjet := hlocal.iteratedDeriv_eq order
    simpa only [iteratedDeriv_const_mul_field, polynomial_iteratedDeriv_eval] using hjet
  exact hinterior.of_subset_closure hleftContinuous
    (continuous_const.mul (Polynomial.derivative^[order] forcing).continuous).continuousOn
    (fun p hp => ⟨hp.1.le, hp.2.le⟩) (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])

theorem first_jet_of_polynomial_equation
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization p : ℝ)
    (hregular : DifferentiableAt ℝ density p)
    (hnext : DifferentiableAt ℝ density (crossing.eval p))
    (hjet : iteratedDeriv 1 (fun q => mass * density q - density (crossing.eval q)) p =
      normalization * forcing.derivative.eval p) :
    mass * deriv density p = crossing.derivative.eval p * deriv density (crossing.eval p) +
      normalization * forcing.derivative.eval p := by
  have hleft := (hregular.hasDerivAt.const_mul mass).sub
    (hnext.hasDerivAt.comp p (crossing.hasDerivAt p))
  rw [iteratedDeriv_one] at hjet
  change deriv ((fun q => mass * density q) - density ∘ crossing.eval) p = _ at hjet
  rw [hleft.deriv] at hjet
  nlinarith

theorem second_jet_of_polynomial_equation
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization p : ℝ)
    (hregular : ContDiffAt ℝ 2 density p) (hnext : ContDiffAt ℝ 2 density (crossing.eval p))
    (hjet : iteratedDeriv 2 (fun q => mass * density q - density (crossing.eval q)) p =
      normalization * forcing.derivative.derivative.eval p) :
    mass * iteratedDeriv 2 density p =
      crossing.derivative.eval p ^ 2 * iteratedDeriv 2 density (crossing.eval p) +
        crossing.derivative.derivative.eval p * deriv density (crossing.eval p) +
          normalization * forcing.derivative.derivative.eval p := by
  have hcrossing : ContDiffAt ℝ 2 crossing.eval p :=
    ((AnalyticOnNhd.eval_polynomial crossing) p (mem_univ _)).contDiffAt
  change iteratedDeriv 2 ((fun q => mass * density q) - density ∘ crossing.eval) p = _ at hjet
  rw [iteratedDeriv_sub (contDiffAt_const.mul hregular) (hnext.comp p hcrossing),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_two hnext hcrossing] at hjet
  simp only [Polynomial.deriv, polynomial_iteratedDeriv_eval,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at hjet
  nlinarith

theorem third_jet_of_polynomial_equation
    (density : ℝ → ℝ) (crossing forcing : Polynomial ℝ) (mass normalization p : ℝ)
    (hregular : ContDiffAt ℝ 3 density p) (hnext : ContDiffAt ℝ 3 density (crossing.eval p))
    (hjet : iteratedDeriv 3 (fun q => mass * density q - density (crossing.eval q)) p =
      normalization * forcing.derivative.derivative.derivative.eval p) :
    mass * iteratedDeriv 3 density p =
      crossing.derivative.eval p ^ 3 * iteratedDeriv 3 density (crossing.eval p) +
        3 * crossing.derivative.eval p * crossing.derivative.derivative.eval p *
          iteratedDeriv 2 density (crossing.eval p) +
        crossing.derivative.derivative.derivative.eval p * deriv density (crossing.eval p) +
          normalization * forcing.derivative.derivative.derivative.eval p := by
  have hcrossing : ContDiffAt ℝ 3 crossing.eval p :=
    ((AnalyticOnNhd.eval_polynomial crossing) p (mem_univ _)).contDiffAt
  change iteratedDeriv 3 ((fun q => mass * density q) - density ∘ crossing.eval) p = _ at hjet
  rw [iteratedDeriv_sub (contDiffAt_const.mul hregular) (hnext.comp p hcrossing),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_three hnext hcrossing] at hjet
  simp only [Polynomial.deriv, polynomial_iteratedDeriv_eval,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at hjet
  nlinarith

end
end Universality
