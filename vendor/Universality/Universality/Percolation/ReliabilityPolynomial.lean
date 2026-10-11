import Universality.Percolation.Bernoulli
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-!
# The graph crossing polynomial

Each configuration contributes its independent Bernoulli product.  The
polynomial is defined by this finite experiment and subsequently evaluated in
the reals.  No threshold or uniqueness property is built into its definition.
-/

namespace Universality
namespace FiniteNetwork
open Polynomial

variable {vertices edges : ℕ}

def openCount (ω : Configuration edges) : ℕ :=
  (Finset.univ.filter fun e : Fin edges => ω e = true).card

def crossingCountBySize (R : FiniteNetwork vertices edges) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun ω : Configuration edges =>
    R.crosses ω = true ∧ openCount ω = k).card

theorem openCount_le (ω : Configuration edges) : openCount ω ≤ edges := by
  simpa [openCount] using Finset.card_filter_le (Finset.univ : Finset (Fin edges))
    (fun e => ω e = true)

theorem configurationPolynomial_eq (ω : Configuration edges) :
    (∏ e : Fin edges, if ω e then (X : Polynomial ℚ) else 1 - X) =
      X ^ openCount ω * (1 - X) ^ (edges - openCount ω) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun e : Fin edges => ω e = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hcard : (Finset.univ.filter fun e : Fin edges => ¬ ω e = true).card =
      edges - openCount ω := by
    unfold openCount
    omega
  rw [hcard]
  rfl

noncomputable def reliabilityPolynomial (R : FiniteNetwork vertices edges) : Polynomial ℚ :=
  ∑ ω : Configuration edges,
    if R.crosses ω then ∏ e : Fin edges, if ω e then X else 1 - X else 0

theorem reliabilityPolynomial_bernstein (R : FiniteNetwork vertices edges) :
    R.reliabilityPolynomial = ∑ k ∈ Finset.range (edges + 1),
      (R.crossingCountBySize k : Polynomial ℚ) * X ^ k * (1 - X) ^ (edges - k) := by
  unfold reliabilityPolynomial
  simp only [configurationPolynomial_eq]
  rw [← Finset.sum_filter]
  have hmap : ∀ ω ∈ (Finset.univ.filter fun ω : Configuration edges => R.crosses ω = true),
      openCount ω ∈ Finset.range (edges + 1) := by
    intro ω _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (openCount_le ω))
  rw [← Finset.sum_fiberwise_of_maps_to' hmap
    (fun k => (X : Polynomial ℚ) ^ k * (1 - X) ^ (edges - k))]
  apply Finset.sum_congr rfl
  intro k _
  simp [crossingCountBySize, Finset.filter_filter, nsmul_eq_mul, mul_assoc]

theorem reliabilityPolynomial_eval (R : FiniteNetwork vertices edges) (p : ℝ) :
    R.reliabilityPolynomial.eval₂ (Rat.castHom ℝ) p = R.reliability p := by
  simp only [reliabilityPolynomial, reliability, bernoulliWeight,
    eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro ω _
  split
  · simp only [eval₂_finsetProd]
    apply Finset.prod_congr rfl
    intro e _
    split <;> simp_all
  · simp

end FiniteNetwork
end Universality
