import Universality.Percolation.ProductDisintegration

namespace Universality
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem two_level_product_mass {I J Ω : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype Ω]
    (weight : I → J → Ω → ℝ) (hnormalized : ∀ i j, ∑ x, weight i j x = 1) :
    (∑ outcome : I → J → Ω, ∏ i, ∏ j, weight i j (outcome i j)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (i : I) (row : J → Ω) => ∏ j, weight i j (row j))]
  have hrow (i : I) : (∑ row : J → Ω, ∏ j, weight i j (row j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hnormalized, Finset.prod_const_one]
  simp only [hrow, Finset.prod_const_one]

theorem two_level_product_local_moment {I J Ω : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype Ω]
    (weight : I → J → Ω → ℝ) (hnormalized : ∀ i j, ∑ x, weight i j x = 1)
    (response : Ω → ℝ) (first : I) (second : J) :
    (∑ outcome : I → J → Ω, (∏ i, ∏ j, weight i j (outcome i j)) * response (outcome first second)) =
      ∑ x, weight first second x * response x := by
  classical
  have hrow (i : I) : (∑ row : J → Ω, ∏ j, weight i j (row j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hnormalized, Finset.prod_const_one]
  rw [finite_product_local_moment (fun (i : I) (row : J → Ω) => ∏ j, weight i j (row j))
    (fun (row : J → Ω) => response (row second)) first]
  simp only [hrow, Finset.prod_const_one, one_mul]
  rw [finite_product_local_moment (weight first) response second]
  simp only [hnormalized, Finset.prod_const_one, one_mul]

theorem three_level_product_local_moment {I J K Ω : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Fintype Ω]
    (weight : I → J → K → Ω → ℝ) (hnormalized : ∀ i j k, ∑ x, weight i j k x = 1)
    (response : Ω → ℝ) (first : I) (second : J) (third : K) :
    (∑ outcome : I → J → K → Ω,
      (∏ i, ∏ j, ∏ k, weight i j k (outcome i j k)) * response (outcome first second third)) =
      ∑ x, weight first second third x * response x := by
  classical
  have hrow (i : I) : (∑ row : J → K → Ω, ∏ j, ∏ k, weight i j k (row j k)) = 1 :=
    two_level_product_mass (weight i) (hnormalized i)
  rw [finite_product_local_moment (fun (i : I) (row : J → K → Ω) => ∏ j, ∏ k, weight i j k (row j k))
    (fun (row : J → K → Ω) => response (row second third)) first]
  simp only [hrow, Finset.prod_const_one, one_mul]
  exact two_level_product_local_moment (weight first) (hnormalized first) response second third

end
end Universality


