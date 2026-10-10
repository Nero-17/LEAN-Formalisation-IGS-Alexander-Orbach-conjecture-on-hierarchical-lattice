import Universality.Percolation.ClusterNumberBoundary
import Universality.Analysis.DiscountedIteration

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem internalClusterFamily_card_le (configuration : Configuration edges) :
    (R.internalClusterFamily configuration).card ≤ vertices := by
  apply (Finset.card_filter_le _ _).trans
  apply (Finset.card_image_le).trans
  simp only [Finset.card_univ, Fintype.card_fin, le_refl]

theorem expectedInternalClusterNumber_bounds {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ R.expectedInternalClusterNumber p ∧ R.expectedInternalClusterNumber p ≤ vertices := by
  constructor
  · exact Finset.sum_nonneg (fun configuration _ =>
      mul_nonneg (bernoulliWeight_nonneg hp hp' _) (Nat.cast_nonneg _))
  · calc
      _ ≤ ∑ configuration : Configuration edges, bernoulliWeight p configuration * (vertices : ℝ) := by
        apply Finset.sum_le_sum
        intro configuration _
        apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
        exact_mod_cast R.internalClusterFamily_card_le configuration
      _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

def unitReliability (p : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨R.reliability p.val, R.reliability_nonneg p.property.1 p.property.2,
    R.reliability_le_one p.property.1 p.property.2⟩

/-- The candidate density defined by the convergent cluster-number series.
Its identification with the volume limit is a separate theorem. -/
def clusterNumberSeries (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) *
    discountedIteration R.unitReliability (fun q => R.expectedInternalClusterNumber q.val) (1 / (edges : ℝ)) p

theorem clusterNumberSeries_bounded (hedges : 1 < edges) :
    ∃ bound : ℝ, ∀ p : Set.Icc (0 : ℝ) 1, |R.clusterNumberSeries p| ≤ bound := by
  have hm : (1 : ℝ) < edges := by exact_mod_cast hedges
  refine ⟨|((edges : ℝ) - 1) / ((vertices : ℝ) - 2)| *
    ((1 / (edges : ℝ)) * vertices / (1 - 1 / (edges : ℝ))), ?_⟩
  intro p
  unfold clusterNumberSeries
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply discountedIteration_bound R.unitReliability _ _ (vertices : ℝ)
    (one_div_nonneg.mpr (lt_trans zero_lt_one hm).le) ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
  intro q
  rw [abs_of_nonneg (R.expectedInternalClusterNumber_bounds q.property.1 q.property.2).1]
  exact (R.expectedInternalClusterNumber_bounds q.property.1 q.property.2).2

theorem clusterNumberSeries_equation (hedges : 1 < edges) (p : Set.Icc (0 : ℝ) 1) :
    (edges : ℝ) * R.clusterNumberSeries p - R.clusterNumberSeries (R.unitReliability p) =
      ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) * R.expectedInternalClusterNumber p.val := by
  have hm : (1 : ℝ) < edges := by exact_mod_cast hedges
  have h := discountedIteration_equation R.unitReliability
    (fun q => R.expectedInternalClusterNumber q.val) (1 / (edges : ℝ)) (vertices : ℝ)
    (one_div_nonneg.mpr (lt_trans zero_lt_one hm).le) ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
    (fun q => by rw [abs_of_nonneg (R.expectedInternalClusterNumber_bounds q.property.1 q.property.2).1]
                 exact (R.expectedInternalClusterNumber_bounds q.property.1 q.property.2).2) p
  have hne : (edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  field_simp [hne] at h
  unfold clusterNumberSeries
  linear_combination ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) * h

theorem clusterNumberSeries_unique (hedges : 1 < edges)
    (solution : Set.Icc (0 : ℝ) 1 → ℝ) (bound : ℝ)
    (hbound : ∀ p, |solution p| ≤ bound)
    (hequation : ∀ p, (edges : ℝ) * solution p - solution (R.unitReliability p) =
      ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) * R.expectedInternalClusterNumber p.val) :
    solution = R.clusterNumberSeries := by
  have hm : (1 : ℝ) < edges := by exact_mod_cast hedges
  have hne : (edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  obtain ⟨seriesBound, hseriesBound⟩ := R.clusterNumberSeries_bounded hedges
  apply discounted_equation_unique R.unitReliability
    (fun p => ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) * R.expectedInternalClusterNumber p.val)
    solution R.clusterNumberSeries (1 / (edges : ℝ)) bound seriesBound
    (one_div_nonneg.mpr (lt_trans zero_lt_one hm).le) ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
    hbound hseriesBound
  · intro p
    have h := hequation p
    rw [div_mul_eq_mul_div] at h
    field_simp [hne]
    linarith
  · intro p
    have h := R.clusterNumberSeries_equation hedges p
    rw [div_mul_eq_mul_div] at h
    field_simp [hne]
    linarith

end
end Universality.FiniteNetwork
