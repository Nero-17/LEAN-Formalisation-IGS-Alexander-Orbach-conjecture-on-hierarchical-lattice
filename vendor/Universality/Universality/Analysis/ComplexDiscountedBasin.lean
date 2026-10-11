import Universality.Analysis.ComplexDiscountedIteration
import Mathlib.Analysis.Analytic.Composition

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

theorem complexDiscountedIteration_finite_shift (iteration forcing : ℂ → ℂ)
    (discount point : ℂ) (depth : ℕ)
    (htail : Summable (fun n : ℕ => discount ^ (n + 1) *
      forcing (iteration^[n] (iteration^[depth] point)))) :
    complexDiscountedIteration iteration forcing discount point =
      (∑ n ∈ Finset.range depth, discount ^ (n + 1) * forcing (iteration^[n] point)) +
        discount ^ depth * complexDiscountedIteration iteration forcing discount
          (iteration^[depth] point) := by
  have hterm (n : ℕ) : discount ^ (n + depth + 1) * forcing (iteration^[n + depth] point) =
      discount ^ depth * (discount ^ (n + 1) * forcing (iteration^[n] (iteration^[depth] point))) := by
    rw [Function.iterate_add_apply]
    rw [show n + depth + 1 = depth + (n + 1) by omega, pow_add]
    ring
  have hshift := (htail.mul_left (discount ^ depth)).congr (fun n => (hterm n).symm)
  have hfull : Summable (fun n : ℕ => discount ^ (n + 1) * forcing (iteration^[n] point)) :=
    (summable_nat_add_iff depth).mp hshift
  unfold complexDiscountedIteration
  rw [← hfull.sum_add_tsum_nat_add depth]
  simp only [hterm, tsum_mul_left]

/-- Analyticity propagates backward through every finite number of iterations
from an invariant open domain on which the forcing is uniformly bounded. -/
theorem complexDiscountedIteration_analyticAt_of_enters
    (iteration forcing : ℂ → ℂ) (discount : ℂ) (domain : Set ℂ) (bound : ℝ)
    (hdiscount : ‖discount‖ < 1) (hopen : IsOpen domain)
    (hiteration : Differentiable ℂ iteration) (hforcing : Differentiable ℂ forcing)
    (hmaps : MapsTo iteration domain domain)
    (hbound : ∀ point ∈ domain, ‖forcing point‖ ≤ bound)
    (point : ℂ) (depth : ℕ) (hpoint : iteration^[depth] point ∈ domain) :
    AnalyticAt ℂ (complexDiscountedIteration iteration forcing discount) point := by
  have hseries := complexDiscountedIteration_analyticOnNhd iteration forcing discount domain bound
    hdiscount hopen hiteration.differentiableOn hforcing.differentiableOn hmaps hbound
  have hprefix : AnalyticAt ℂ (fun z => ∑ n ∈ Finset.range depth,
      discount ^ (n + 1) * forcing (iteration^[n] z)) point := by
    apply Finset.analyticAt_fun_sum
    intro n _
    exact analyticAt_const.mul ((hforcing.analyticAt _).comp ((hiteration.iterate n).analyticAt _))
  have htail : AnalyticAt ℂ (fun z => discount ^ depth *
      complexDiscountedIteration iteration forcing discount (iteration^[depth] z)) point :=
    analyticAt_const.mul ((hseries _ hpoint).comp ((hiteration.iterate depth).analyticAt _))
  apply (hprefix.add htail).congr
  have heventually : ∀ᶠ z in 𝓝 point, iteration^[depth] z ∈ domain :=
    (hiteration.iterate depth).continuous.continuousAt.eventually (hopen.mem_nhds hpoint)
  filter_upwards [heventually] with z hz
  exact (complexDiscountedIteration_finite_shift iteration forcing discount z depth
    (complexDiscountedIteration_summable iteration forcing discount domain bound
      hdiscount hmaps hbound _ hz)).symm

end
end Universality
