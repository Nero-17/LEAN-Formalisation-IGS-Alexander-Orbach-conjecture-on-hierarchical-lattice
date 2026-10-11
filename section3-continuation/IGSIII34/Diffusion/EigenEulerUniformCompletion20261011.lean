import IGSIII34.Diffusion.EigenEulerConvergenceCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

/-- A uniformly vanishing generator error is sufficient. No artificially
chosen error sequence or time-integral convergence is an input. -/
theorem eigenEuler_uniform_recursion_tendsto_completion20261011
    (scales : ℕ → ℝ) (scalePositive : ∀ depth, 0 < scales depth)
    (diverges : Tendsto scales atTop atTop)
    (steps : ℕ → ℕ) (time : ℝ)
    (timeLimit : Tendsto (fun depth => (steps depth : ℝ) / scales depth) atTop (𝓝 time))
    (eigenvalue : ℝ) (eigenvalueNonnegative : 0 ≤ eigenvalue)
    (values : ℕ → ℕ → ℝ) (initial : ℝ)
    (initialLimit : Tendsto (fun depth => values depth 0) atTop (𝓝 initial))
    (recursion : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ step,
      |values depth (step + 1) - (1 - eigenvalue / scales depth) * values depth step| ≤ tolerance / scales depth) :
    Tendsto (fun depth => values depth (steps depth)) atTop (𝓝 (Real.exp (-eigenvalue * time) * initial)) := by
  have geometric := (eigenEuler_geometric_tendsto_completion20261011 scales diverges steps time timeLimit eigenvalue eigenvalueNonnegative).mul initialLimit
  have differenceVanish : Tendsto
      (fun depth => values depth (steps depth) - (1 - eigenvalue / scales depth) ^ steps depth * values depth 0)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance tolerancePositive
    have denominatorPositive : 0 < |time| + 1 := by positivity
    have reducedPositive : 0 < tolerance / (|time| + 1) := div_pos tolerancePositive denominatorPositive
    have timeBelow : time < |time| + 1 := by linarith [le_abs_self time]
    filter_upwards [recursion (tolerance / (|time| + 1)) reducedPositive,
      diverges.eventually (eventually_ge_atTop eigenvalue),
      timeLimit.eventually (eventually_lt_nhds timeBelow)] with depth recursionBound large timeBound
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ (steps depth : ℝ) * ((tolerance / (|time| + 1)) / scales depth) :=
        eigenEuler_discrete_error_completion20261011 (values depth) (1 - eigenvalue / scales depth)
          ((tolerance / (|time| + 1)) / scales depth)
          (sub_nonneg.mpr ((div_le_one (scalePositive depth)).mpr large))
          (sub_le_self _ (div_nonneg eigenvalueNonnegative (scalePositive depth).le))
          (div_nonneg reducedPositive.le (scalePositive depth).le) recursionBound (steps depth)
      _ = (tolerance / (|time| + 1)) * ((steps depth : ℝ) / scales depth) := by ring
      _ < (tolerance / (|time| + 1)) * (|time| + 1) := mul_lt_mul_of_pos_left timeBound reducedPositive
      _ = tolerance := by field_simp
  simpa only [sub_add_cancel, zero_add] using differenceVanish.add geometric

end
end IGSIII34.Diffusion
