import Universality.Arithmetic.SixExponentials
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.RingTheory.Algebraic.Basic

namespace Universality.Section4

theorem six_exponentials_real (first : Fin 2 → ℝ) (second : Fin 3 → ℝ)
    (hfirst : LinearIndependent ℚ first)
    (hsecond : LinearIndependent ℚ second) :
    ∃ i j, Transcendental ℚ (Real.exp (first i * second j)) := by
  have hfirst' : LinearIndependent ℚ (fun i => (first i : ℂ)) :=
    hfirst.map' (Complex.ofRealAm.toLinearMap.restrictScalars ℚ)
      (LinearMap.ker_eq_bot.mpr Complex.ofReal_injective)
  have hsecond' : LinearIndependent ℚ (fun j => (second j : ℂ)) :=
    hsecond.map' (Complex.ofRealAm.toLinearMap.restrictScalars ℚ)
      (LinearMap.ker_eq_bot.mpr Complex.ofReal_injective)
  obtain ⟨i, j, htranscendental⟩ := External.six_exponentials _ _ hfirst' hsecond'
  refine ⟨i, j, fun halgebraic => htranscendental ?_⟩
  have hmap := halgebraic.algHom (Complex.ofRealAm.restrictScalars ℚ)
  simpa only [AlgHom.restrictScalars_apply, Complex.ofRealAm_coe,
    Complex.ofReal_exp, Complex.ofReal_mul] using hmap

theorem not_linearIndependent_of_algebraic_real_exponentials
    (first : Fin 2 → ℝ) (second : Fin 3 → ℝ)
    (hfirst : LinearIndependent ℚ first)
    (halgebraic : ∀ i j, IsAlgebraic ℚ (Real.exp (first i * second j))) :
    ¬ LinearIndependent ℚ second := by
  intro hsecond
  obtain ⟨i, j, htranscendental⟩ := six_exponentials_real first second hfirst hsecond
  exact htranscendental (halgebraic i j)

end Universality.Section4

#print axioms Universality.Section4.six_exponentials_real
