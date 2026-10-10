import Universality.Analysis.ComplexAttractingIteration
import Universality.Analysis.DiscountedIteration
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace Universality
noncomputable section
open Filter Polynomial
open scoped Topology

theorem polynomial_eval_complex_ofReal (polynomial : Polynomial ℝ) (point : ℝ) :
    (polynomial.map Complex.ofRealHom).eval (point : ℂ) = ((polynomial.eval point : ℝ) : ℂ) :=
  Polynomial.eval_map_apply (p := polynomial) Complex.ofRealHom point

theorem polynomial_complex_iterate_ofReal (polynomial : Polynomial ℝ) (point : ℝ) (n : ℕ) :
    (polynomial.map Complex.ofRealHom).eval^[n] (point : ℂ) =
      ((polynomial.eval^[n] point : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact polynomial_eval_complex_ofReal polynomial _

theorem complexDiscountedIteration_map_real (iteration forcing : Polynomial ℝ)
    (discount point : ℝ) :
    complexDiscountedIteration (iteration.map Complex.ofRealHom).eval
      (forcing.map Complex.ofRealHom).eval (discount : ℂ) (point : ℂ) =
      ((discountedIteration iteration.eval forcing.eval discount point : ℝ) : ℂ) := by
  unfold complexDiscountedIteration discountedIteration
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [polynomial_complex_iterate_ofReal]
  simp only [polynomial_eval_complex_ofReal]
  simp

/-- The real discounted polynomial series is analytic at every real point in
the basin of a zero-derivative fixed point. This gives an actual analytic
extension across endpoint parameters as well as interior analyticity. -/
theorem polynomialDiscountedIteration_analyticAt_of_attracted
    (iteration forcing : Polynomial ℝ) (discount point fixed : ℝ)
    (hdiscount : |discount| < 1) (hfixed : iteration.eval fixed = fixed)
    (hderivative : iteration.derivative.eval fixed = 0)
    (horbit : Tendsto (fun n : ℕ => iteration.eval^[n] point) atTop (𝓝 fixed)) :
    AnalyticAt ℝ (discountedIteration iteration.eval forcing.eval discount) point := by
  have hcomplexFixed : (iteration.map Complex.ofRealHom).eval (fixed : ℂ) = (fixed : ℂ) := by
    rw [polynomial_eval_complex_ofReal, hfixed]
  have hcomplexDerivative : HasDerivAt (iteration.map Complex.ofRealHom).eval 0 (fixed : ℂ) := by
    have h := (iteration.map Complex.ofRealHom).hasDerivAt (fixed : ℂ)
    simpa only [Polynomial.derivative_map, polynomial_eval_complex_ofReal,
      hderivative, Complex.ofReal_zero] using h
  have hcomplexOrbit : Tendsto (fun n : ℕ =>
      (iteration.map Complex.ofRealHom).eval^[n] (point : ℂ)) atTop (𝓝 (fixed : ℂ)) := by
    simpa only [polynomial_complex_iterate_ofReal, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp horbit
  have hcomplex := complexDiscountedIteration_analyticAt_of_attracted
    (iteration.map Complex.ofRealHom).eval (forcing.map Complex.ofRealHom).eval
    (discount : ℂ) (point : ℂ) (fixed : ℂ) (by simpa using hdiscount)
    (iteration.map Complex.ofRealHom).differentiable
    (forcing.map Complex.ofRealHom).differentiable hcomplexFixed hcomplexDerivative hcomplexOrbit
  have hreal := hcomplex.re_ofReal
  have heq : (fun x : ℝ => (complexDiscountedIteration (iteration.map Complex.ofRealHom).eval
      (forcing.map Complex.ofRealHom).eval (discount : ℂ) (x : ℂ)).re) =
      discountedIteration iteration.eval forcing.eval discount := by
    funext x
    rw [complexDiscountedIteration_map_real]
    simp
  rwa [heq] at hreal

end
end Universality
