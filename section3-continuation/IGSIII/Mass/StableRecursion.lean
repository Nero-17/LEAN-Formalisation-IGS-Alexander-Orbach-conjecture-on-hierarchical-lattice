import IGSIII.Mass.BorelCantelli

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace IGSIII.Mass

open Filter
open scoped Topology

/-- A stable scalar recurrence follows the limit of its forcing term. The
proof uses an eventual arithmetic-geometric upper bound on the actual error. -/
theorem tendsto_stable_recursion (sequence forcing : ℕ → ℝ)
    (coefficient forcing_limit : ℝ) (contracting : |coefficient| < 1)
    (recursion : ∀ n, sequence (n + 1) = coefficient * sequence n + forcing n)
    (forcing_converges : Tendsto forcing atTop (𝓝 forcing_limit)) :
    Tendsto sequence atTop (𝓝 (forcing_limit / (1 - coefficient))) := by
  have denominator_nonzero : 1 - coefficient ≠ 0 := by
    have := (le_abs_self coefficient).trans_lt contracting
    linarith
  have fixed_point : coefficient * (forcing_limit / (1 - coefficient)) + forcing_limit =
      forcing_limit / (1 - coefficient) := by
    field_simp
    ring
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerance_positive
  obtain ⟨start, forcing_small⟩ := Metric.tendsto_atTop.mp forcing_converges
    (tolerance * (1 - |coefficient|) / 2) (by positivity)
  have envelope (n : ℕ) :
      |sequence (start + n) - forcing_limit / (1 - coefficient)| ≤
        |coefficient| ^ n * (|sequence start - forcing_limit / (1 - coefficient)| - tolerance / 2) +
          tolerance / 2 := by
    induction n with
    | zero => simp
    | succ n induction_hypothesis =>
      have small := forcing_small (start + n) (by omega)
      rw [Real.dist_eq] at small
      rw [show start + (n + 1) = (start + n) + 1 by omega, recursion]
      have error_identity : coefficient * sequence (start + n) + forcing (start + n) -
          forcing_limit / (1 - coefficient) =
          coefficient * (sequence (start + n) - forcing_limit / (1 - coefficient)) +
            (forcing (start + n) - forcing_limit) := by linarith [fixed_point]
      rw [error_identity]
      apply (abs_add_le _ _).trans
      rw [abs_mul]
      calc
        _ ≤ |coefficient| *
            (|coefficient| ^ n * (|sequence start - forcing_limit / (1 - coefficient)| - tolerance / 2) +
              tolerance / 2) + tolerance * (1 - |coefficient|) / 2 :=
          add_le_add (mul_le_mul_of_nonneg_left induction_hypothesis (abs_nonneg _)) small.le
        _ = _ := by rw [pow_succ]; ring
  have envelope_limit := ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg coefficient) contracting).mul_const
    (|sequence start - forcing_limit / (1 - coefficient)| - tolerance / 2)).add_const (tolerance / 2)
  simp only [zero_mul, zero_add] at envelope_limit
  obtain ⟨tail, envelope_small⟩ := eventually_atTop.mp
    (envelope_limit.eventually (gt_mem_nhds (show tolerance / 2 < tolerance by linarith)))
  refine ⟨start + tail, fun n n_large => ?_⟩
  rw [Real.dist_eq]
  have decomposition : start + (n - start) = n := by omega
  have bound := (envelope (n - start)).trans_lt (envelope_small (n - start) (by omega))
  rwa [decomposition] at bound

end IGSIII.Mass
