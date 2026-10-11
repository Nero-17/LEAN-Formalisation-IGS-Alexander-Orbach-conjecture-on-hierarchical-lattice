import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

def complexDiscountedIteration (iteration forcing : ℂ → ℂ) (discount : ℂ) (point : ℂ) : ℂ :=
  ∑' n : ℕ, discount ^ (n + 1) * forcing (iteration^[n] point)

theorem complexDiscountedIteration_summable (iteration forcing : ℂ → ℂ)
    (discount : ℂ) (domain : Set ℂ) (bound : ℝ)
    (hdiscount : ‖discount‖ < 1) (hmaps : MapsTo iteration domain domain)
    (hbound : ∀ point ∈ domain, ‖forcing point‖ ≤ bound)
    (point : ℂ) (hpoint : point ∈ domain) :
    Summable (fun n : ℕ => discount ^ (n + 1) * forcing (iteration^[n] point)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖discount‖ ^ (n + 1) * bound)
    (((summable_geometric_of_lt_one (norm_nonneg discount) hdiscount).comp_injective
      (fun a b (hab : a + 1 = b + 1) => Nat.add_right_cancel hab)).mul_right bound)
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hbound _ (hmaps.iterate n hpoint))
    (pow_nonneg (norm_nonneg _) _)

theorem complexDiscountedIteration_analyticOnNhd (iteration forcing : ℂ → ℂ)
    (discount : ℂ) (domain : Set ℂ) (bound : ℝ)
    (hdiscount : ‖discount‖ < 1) (hopen : IsOpen domain)
    (hiteration : DifferentiableOn ℂ iteration domain)
    (hforcing : DifferentiableOn ℂ forcing domain)
    (hmaps : MapsTo iteration domain domain)
    (hbound : ∀ point ∈ domain, ‖forcing point‖ ≤ bound) :
    AnalyticOnNhd ℂ (complexDiscountedIteration iteration forcing discount) domain := by
  apply DifferentiableOn.analyticOnNhd _ hopen
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => ‖discount‖ ^ (n + 1) * bound)
    (((summable_geometric_of_lt_one (norm_nonneg discount) hdiscount).comp_injective
      (fun a b (hab : a + 1 = b + 1) => Nat.add_right_cancel hab)).mul_right bound)
    ?_ hopen ?_
  · intro n
    exact (hforcing.comp (hiteration.iterate hmaps n) (hmaps.iterate n)).const_mul _
  · intro n point hpoint
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hbound _ (hmaps.iterate n hpoint))
      (pow_nonneg (norm_nonneg _) _)

end
end Universality
