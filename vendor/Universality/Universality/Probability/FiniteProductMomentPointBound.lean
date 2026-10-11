import Universality.Probability.FiniteProductPointBounds
import Universality.Probability.FiniteConvolutionMomentPointBound

namespace Universality
noncomputable section

theorem finite_product_two_live_point_bound {index values : Type*} [Fintype index] [DecidableEq index]
    [Fintype values] (weight : index → values → ℝ) (mass : index → values → ℕ)
    (hweight : ∀ i value, 0 ≤ weight i value) (hnormalized : ∀ i, ∑ value, weight i value = 1)
    (first second : index) (hdistinct : second ≠ first)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hfirstPoint : ∀ size : ℕ, (∑ value, if mass first value = size then weight first value else 0) ≤ bound)
    (hsecondPoint : ∀ size : ℕ, (∑ value, if mass second value = size then weight second value else 0) ≤ bound)
    (shift order size : ℕ) :
    (size : ℝ) ^ order *
      (∑ configuration : index → values, if shift + ∑ i, mass i (configuration i) = size
        then (∏ i, weight i (configuration i)) else 0) ≤
      2 ^ (order + 1) * bound *
        (∑ configuration : index → values, (∏ i, weight i (configuration i)) *
          ((shift + ∑ i, mass i (configuration i) : ℕ) : ℝ) ^ order) := by
  classical
  let restWeight (rest : {i // i ≠ first} → values) := ∏ i : {i // i ≠ first}, weight i (rest i)
  let restMass (rest : {i // i ≠ first} → values) := shift + ∑ i : {i // i ≠ first}, mass i (rest i)
  have hrestNormalized : ∑ rest, restWeight rest = 1 := by
    dsimp only [restWeight]
    rw [← Fintype.prod_sum]
    simp only [hnormalized, Finset.prod_const_one]
  have hrestPoint (target : ℕ) : (∑ rest, if restMass rest = target then restWeight rest else 0) ≤ bound :=
    finite_product_atom_bound (fun i : {i // i ≠ first} => weight i)
      (fun i : {i // i ≠ first} => mass i) (fun i => hweight i) (fun i => hnormalized i)
      ⟨second, hdistinct⟩ bound hsecondPoint shift target
  have hpoint := finite_convolution_point_bound_by_moment (weight first) restWeight
    (mass first) restMass bound hbound (hweight first)
    (fun rest => Finset.prod_nonneg (fun i _ => hweight i (rest i)))
    (hnormalized first) hrestNormalized hfirstPoint hrestPoint order size
  have hatom := finite_product_split_observable weight mass first
    (fun total => if shift + total = size then 1 else 0)
  have hmoment := finite_product_split_observable weight mass first
    (fun total => ((shift + total : ℕ) : ℝ) ^ order)
  simp only [mul_ite, mul_one, mul_zero] at hatom
  rw [hatom, hmoment]
  simpa only [restWeight, restMass, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_ite, mul_one, mul_zero] using hpoint

end
end Universality
