import Universality.Graph.CrossingOpenCount

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_le_distance_power (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    R.reliability p ≤ (2 : ℝ) ^ edges * p ^ R.fullGraph.dist R.source R.target := by
  unfold reliability
  calc
    _ ≤ ∑ _ : Configuration edges, p ^ R.fullGraph.dist R.source R.target := by
      apply Finset.sum_le_sum
      intro configuration _
      split_ifs with hcross
      · rw [bernoulliWeight_eq_bernstein]
        calc
          _ ≤ p ^ openCount configuration := mul_le_of_le_one_right (pow_nonneg hp _)
            (pow_le_one₀ (sub_nonneg.mpr hp') (by linarith))
          _ ≤ _ := pow_le_pow_of_le_one hp hp' (R.distance_le_openCount configuration hcross)
      · exact pow_nonneg hp _
    _ = _ := by simp [Configuration, Fintype.card_fun, nsmul_eq_mul]

theorem distance_power_le_reliability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    p ^ R.fullGraph.dist R.source R.target * (1 - p) ^ edges ≤ R.reliability p := by
  obtain ⟨configuration, hcross, hsize⟩ := R.exists_crossing_configuration_minimum_size hsimple hconnected
  calc
    _ ≤ p ^ R.fullGraph.dist R.source R.target * (1 - p) ^ (edges - openCount configuration) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (sub_nonneg.mpr hp') (by linarith) (Nat.sub_le _ _)) (pow_nonneg hp _)
    _ = bernoulliWeight p configuration := by rw [bernoulliWeight_eq_bernstein, hsize]
    _ ≤ R.reliability p := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun configuration : Configuration edges => if R.crosses configuration then bernoulliWeight p configuration else 0)
        (fun other _ => by split_ifs; exact bernoulliWeight_nonneg hp hp' _; exact le_rfl)
        (Finset.mem_univ configuration)
      simpa only [reliability, hcross, ↓reduceIte] using h

theorem reliability_distance_ratio_bounds (p upper : ℝ) (hp : 0 < p) (hpu : p ≤ upper) (hu : upper < 1)
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    (1 - upper) ^ edges ≤ R.reliability p / p ^ R.fullGraph.dist R.source R.target ∧
      R.reliability p / p ^ R.fullGraph.dist R.source R.target ≤ (2 : ℝ) ^ edges := by
  have hp' : p ≤ 1 := (hpu.trans_lt hu).le
  constructor
  · apply (le_div_iff₀ (pow_pos hp _)).mpr
    calc
      _ ≤ (1 - p) ^ edges * p ^ R.fullGraph.dist R.source R.target :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sub_pos.mpr hu).le (by linarith) edges) (pow_nonneg hp.le _)
      _ ≤ _ := by simpa only [mul_comm] using R.distance_power_le_reliability p hp.le hp' hsimple hconnected
  · exact (div_le_iff₀ (pow_pos hp _)).mpr (R.reliability_le_distance_power p hp.le hp')

end
end Universality.FiniteNetwork
