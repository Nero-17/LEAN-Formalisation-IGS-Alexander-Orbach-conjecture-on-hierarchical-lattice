import IGSIII.Chemical.SmallBall.PositiveMoments
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Sym.Card

/-! The factorial majorant uses weak compositions, rather than assignments
of individual factors.  The multinomial coefficient cancels the product of
the lower-order factorials exactly. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open scoped BigOperators

noncomputable section

variable {Edge Outcome : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

theorem finite_product_sum_moment_multinomial (weight value : Edge → Outcome → ℝ) (power : ℕ) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge, value edge (outcome edge)) ^ power) =
      ∑ orders ∈ Finset.piAntidiag (Finset.univ : Finset Edge) power,
        (Nat.multinomial Finset.univ orders : ℝ) *
          ∏ edge, ∑ outcome, weight edge outcome * value edge outcome ^ orders edge := by
  classical
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro orders _
  have rearrange (outcome : Edge → Outcome) :
      (∏ edge, weight edge (outcome edge)) *
        ((Nat.multinomial Finset.univ orders : ℝ) *
          ∏ edge, value edge (outcome edge) ^ orders edge) =
      (Nat.multinomial Finset.univ orders : ℝ) *
        ((∏ edge, weight edge (outcome edge)) * ∏ edge, value edge (outcome edge) ^ orders edge) := by
    ring
  simp_rw [rearrange]
  rw [← Finset.mul_sum, Universality.finite_product_mixed_moment]

theorem cardinal_weak_compositions (power : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset Edge) power).card =
      (Fintype.card Edge + power - 1).choose power := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
    Finset.card_univ, Sym.card_sym_eq_choose]

theorem finite_product_sum_moment_factorial_bound (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (power : ℕ) {constant : ℝ}
    (momentBound : ∀ edge order, order ≤ power →
      (∑ outcome, weight edge outcome * value edge outcome ^ order) ≤
        constant ^ order * (order.factorial : ℝ)) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge, value edge (outcome edge)) ^ power) ≤
      ((Fintype.card Edge + power - 1).choose power : ℝ) *
        (constant ^ power * (power.factorial : ℝ)) := by
  classical
  rw [finite_product_sum_moment_multinomial]
  have termBound (orders : Edge → ℕ)
      (within : orders ∈ Finset.piAntidiag (Finset.univ : Finset Edge) power) :
      (Nat.multinomial Finset.univ orders : ℝ) *
          (∏ edge, ∑ outcome, weight edge outcome * value edge outcome ^ orders edge) ≤
        constant ^ power * (power.factorial : ℝ) := by
    have sumOrders := (Finset.mem_piAntidiag.mp within).1
    have productBound :
        (∏ edge, ∑ outcome, weight edge outcome * value edge outcome ^ orders edge) ≤
        ∏ edge, constant ^ orders edge * ((orders edge).factorial : ℝ) := by
      apply Finset.prod_le_prod
        (fun edge _ => Finset.sum_nonneg (fun outcome _ =>
          mul_nonneg (weightNonnegative edge outcome) (pow_nonneg (valueNonnegative edge outcome) _)))
      intro edge _
      apply momentBound edge
      rw [← sumOrders]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ edge)
    have factorialIdentity : (Nat.multinomial Finset.univ orders : ℝ) *
        (∏ edge, ((orders edge).factorial : ℝ)) = (power.factorial : ℝ) := by
      have identity := Nat.multinomial_spec (Finset.univ : Finset Edge) orders
      rw [sumOrders] at identity
      exact_mod_cast (by simpa only [mul_comm] using identity)
    calc
      _ ≤ (Nat.multinomial Finset.univ orders : ℝ) *
          ∏ edge, constant ^ orders edge * ((orders edge).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left productBound (Nat.cast_nonneg _)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sumOrders]
        calc
          _ = constant ^ power * ((Nat.multinomial Finset.univ orders : ℝ) *
              ∏ edge, ((orders edge).factorial : ℝ)) := by ring
          _ = _ := by rw [factorialIdentity]
  calc
    _ ≤ ∑ _orders ∈ Finset.piAntidiag (Finset.univ : Finset Edge) power,
        constant ^ power * (power.factorial : ℝ) := Finset.sum_le_sum termBound
    _ = _ := by rw [Finset.sum_const, cardinal_weak_compositions, nsmul_eq_mul]

theorem finite_product_path_sum_moment_factorial_bound
    (weight value : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (valueNonnegative : ∀ edge outcome, 0 ≤ value edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge) (power : ℕ) {constant : ℝ}
    (momentBound : ∀ edge ∈ path, ∀ order, order ≤ power →
      (∑ outcome, weight edge outcome * value edge outcome ^ order) ≤
        constant ^ order * (order.factorial : ℝ)) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      (∑ edge ∈ path, value edge (outcome edge)) ^ power) ≤
      ((path.card + power - 1).choose power : ℝ) *
        (constant ^ power * (power.factorial : ℝ)) := by
  have restricted := finite_product_restrict_observable weight normalized path
    (fun outcome : path → Outcome => (∑ edge : path, value edge (outcome edge)) ^ power)
  have sumPath (outcome : Edge → Outcome) :
      (∑ edge : path, value edge (outcome edge)) = ∑ edge ∈ path, value edge (outcome edge) :=
    Finset.sum_coe_sort path (fun edge => value edge (outcome edge))
  simp_rw [sumPath] at restricted
  rw [restricted]
  simpa only [Fintype.card_coe] using finite_product_sum_moment_factorial_bound
    (fun edge : path => weight edge) (fun edge : path => value edge)
    (fun edge => weightNonnegative edge) (fun edge => valueNonnegative edge) power
    (fun edge => momentBound edge edge.property)

theorem selected_path_factorial_moment_bound {Root : Type*} [Fintype Root]
    (rootWeight : Root → ℝ) (family : Root → PathFamily Edge)
    (selected : Root → Finset Edge) (selectedMember : ∀ root, selected root ∈ (family root).paths)
    (weight value : Root → Edge → Outcome → ℝ)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (valueNonnegative : ∀ root edge outcome, 0 ≤ value root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    (power : ℕ) {constant : ℝ}
    (momentBound : ∀ root edge, edge ∈ selected root → ∀ order, order ≤ power →
      (∑ outcome, weight root edge outcome * value root edge outcome ^ order) ≤
        constant ^ order * (order.factorial : ℝ)) :
    (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
      (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge)) ^ power) ≤
      (∑ root, rootWeight root * (((selected root).card + power - 1).choose power : ℝ)) *
        (constant ^ power * (power.factorial : ℝ)) := by
  have rootBound (root : Root) :
      (∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
        (family root).shortest (fun edge => value root edge (outcome edge)) ^ power) ≤
      (((selected root).card + power - 1).choose power : ℝ) *
        (constant ^ power * (power.factorial : ℝ)) := by
    calc
      _ ≤ ∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
          (∑ edge ∈ selected root, value root edge (outcome edge)) ^ power := by
        apply Finset.sum_le_sum
        intro outcome _
        apply mul_le_mul_of_nonneg_left _
          (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
        exact pow_le_pow_left₀
          ((family root).shortest_nonneg (fun edge => valueNonnegative root edge (outcome edge)))
          ((family root).shortest_le_pathCost _ (selectedMember root)) power
      _ ≤ _ := finite_product_path_sum_moment_factorial_bound (weight root) (value root)
        (weightNonnegative root) (valueNonnegative root) (normalized root) (selected root)
        power (momentBound root)
  calc
    _ ≤ ∑ root, rootWeight root *
        ((((selected root).card + power - 1).choose power : ℝ) *
          (constant ^ power * (power.factorial : ℝ))) := Finset.sum_le_sum
      (fun root _ => mul_le_mul_of_nonneg_left (rootBound root) (rootNonnegative root))
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end
end IGSIII.Chemical.SmallBall
