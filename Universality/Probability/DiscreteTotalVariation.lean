import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- For discrete probability laws, pointwise convergence to a law of total
mass one implies convergence in total variation. -/
theorem discrete_probability_total_variation {Index Parameter : Type*}
    (filter : Filter Parameter) (probabilities : Parameter → Index → ℝ) (limit : Index → ℝ)
    (hnonneg : ∀ n k, 0 ≤ probabilities n k) (hlimitNonneg : ∀ k, 0 ≤ limit k)
    (hsum : ∀ n, HasSum (probabilities n) 1) (hlimitSum : HasSum limit 1)
    (hpointwise : ∀ k, Tendsto (fun n => probabilities n k) filter (𝓝 (limit k))) :
    Tendsto (fun n => ∑' k, |probabilities n k - limit k|) filter (𝓝 0) := by
  have hminBound (n : Parameter) (k : Index) : ‖min (probabilities n k) (limit k)‖ ≤ limit k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnonneg n k) (hlimitNonneg k))]
    exact min_le_right _ _
  have hminSum (n : Parameter) : Summable (fun k => min (probabilities n k) (limit k)) :=
    hlimitSum.summable.of_norm_bounded (hminBound n)
  have hminLimit : Tendsto (fun n => ∑' k, min (probabilities n k) (limit k)) filter (𝓝 1) := by
    rw [← hlimitSum.tsum_eq]
    apply tendsto_tsum_of_dominated_convergence hlimitSum.summable
    · intro k
      simpa only [min_self] using (hpointwise k).min
        (tendsto_const_nhds : Tendsto (fun _ : Parameter => limit k) filter (𝓝 (limit k)))
    · exact Eventually.of_forall hminBound
  have hidentity (n : Parameter) : (∑' k, |probabilities n k - limit k|) =
      1 + 1 - 2 * ∑' k, min (probabilities n k) (limit k) := by
    have hpoint (k : Index) : |probabilities n k - limit k| =
        probabilities n k + limit k - 2 * min (probabilities n k) (limit k) := by
      rcases le_total (probabilities n k) (limit k) with hle | hle
      · rw [abs_of_nonpos (sub_nonpos.mpr hle), min_eq_left hle]
        ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle), min_eq_right hle]
        ring
    simp_rw [hpoint]
    rw [((hsum n).summable.add hlimitSum.summable).tsum_sub ((hminSum n).mul_left 2),
      (hsum n).summable.tsum_add hlimitSum.summable, tsum_mul_left,
      (hsum n).tsum_eq, hlimitSum.tsum_eq]
  simp_rw [hidentity]
  convert (tendsto_const_nhds : Tendsto (fun _ : Parameter => (1 : ℝ) + 1)
    filter (𝓝 (1 + 1))).sub (hminLimit.const_mul 2) using 1 <;> norm_num

end
end Universality
