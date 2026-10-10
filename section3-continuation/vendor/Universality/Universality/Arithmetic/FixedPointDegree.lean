import Universality.Arithmetic.GraphFixedPointCoefficients

/-!
The exact leading-coefficient obligation for the standalone full-degree claim.
The degree bound and alternating configuration formula are proved for actual
finite networks. Nonvanishing from canonicality is not assumed to be proved.
-/

namespace Universality.FiniteNetwork

noncomputable section
open Polynomial

variable {vertices edges : ℕ}

theorem integer_configurationPolynomial_natDegree_le (configuration : Configuration edges) :
    (∏ edge : Fin edges, if configuration edge then (X : ℤ[X]) else 1 - X).natDegree ≤ edges := by
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ edge : Fin edges, (if configuration edge then (X : ℤ[X]) else 1 - X).natDegree) ≤
        ∑ _edge : Fin edges, 1 := by
      apply Finset.sum_le_sum
      intro edge _
      cases configuration edge
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact natDegree_sub_le _ _ |>.trans (by simp)
      · simp
    _ = edges := by simp

theorem integerReliabilityPolynomial_natDegree_le_edges (network : FiniteNetwork vertices edges) :
    network.integerReliabilityPolynomial.natDegree ≤ edges := by
  unfold integerReliabilityPolynomial
  apply natDegree_sum_le_of_forall_le
  intro configuration _
  cases network.crosses configuration
  · simp
  · simpa using integer_configurationPolynomial_natDegree_le configuration

theorem integer_configurationPolynomial_coeff_edges (configuration : Configuration edges) :
    (∏ edge : Fin edges, if configuration edge then (X : ℤ[X]) else 1 - X).coeff edges =
      (-1 : ℤ) ^ (edges - openCount configuration) := by
  have hcoeff := coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun edge : Fin edges => if configuration edge then (X : ℤ[X]) else 1 - X) 1 (by
      intro edge _
      cases configuration edge
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact natDegree_sub_le _ _ |>.trans (by simp)
      · simp)
  simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hcoeff
  rw [hcoeff]
  have hfactor (edge : Fin edges) :
      (if configuration edge then (X : ℤ[X]) else 1 - X).coeff 1 =
        if configuration edge then 1 else -1 := by
    cases configuration edge <;> norm_num [Polynomial.coeff_one]
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, one_mul]
  congr 1
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun edge : Fin edges => configuration edge = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  unfold openCount
  omega

theorem integerReliabilityPolynomial_coeff_edges (network : FiniteNetwork vertices edges) :
    network.integerReliabilityPolynomial.coeff edges =
      ∑ configuration : Configuration edges,
        if network.crosses configuration then (-1 : ℤ) ^ (edges - openCount configuration) else 0 := by
  unfold integerReliabilityPolynomial
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro configuration _
  cases network.crosses configuration
  · simp
  · simpa using integer_configurationPolynomial_coeff_edges configuration

/-- This is an exact equivalence, not a proof of canonical nonvanishing. For a
connected nonempty graph it isolates the sole missing combinatorial claim. -/
theorem integerReliabilityPolynomial_full_degree_iff (network : FiniteNetwork vertices edges)
    (hpolynomial : network.integerReliabilityPolynomial ≠ 0) :
    network.integerReliabilityPolynomial.natDegree = edges ↔
      (∑ configuration : Configuration edges,
        if network.crosses configuration then (-1 : ℤ) ^ (edges - openCount configuration) else 0) ≠ 0 := by
  rw [← network.integerReliabilityPolynomial_coeff_edges]
  constructor
  · intro hdegree
    have hcoeff : network.integerReliabilityPolynomial.coeff
        network.integerReliabilityPolynomial.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hpolynomial
    simpa only [hdegree] using hcoeff
  · exact natDegree_eq_of_le_of_coeff_ne_zero (network.integerReliabilityPolynomial_natDegree_le_edges)

end
end Universality.FiniteNetwork

#print axioms Universality.FiniteNetwork.integerReliabilityPolynomial_full_degree_iff



