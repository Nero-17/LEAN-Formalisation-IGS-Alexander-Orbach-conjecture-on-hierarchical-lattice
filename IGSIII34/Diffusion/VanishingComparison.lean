import IGSIII.Geometry.FiniteMassTransport

set_option autoImplicit false

namespace IGSIII34.Diffusion
open Filter
open scoped Topology ENNReal

/-- A finite coarse projection can be fixed first and its fine approximation
then sent to infinity. The resulting conclusion concerns the entire sequence,
without a diagonal subsequence assumption. -/
theorem tendsto_zero_of_shifted_comparison (distance mesh : ℕ → ℝ≥0∞)
    (error : ℕ → ℕ → ℝ≥0∞) (start : ℕ)
    (meshConvergence : Tendsto mesh atTop (𝓝 0))
    (errorConvergence : ∀ age, Tendsto (error age) atTop (𝓝 0))
    (bound : ∀ age, start ≤ age + 1 → ∀ fine,
      distance (fine + (age + 1)) ≤ mesh age + mesh age + error age fine) :
    Tendsto distance atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon epsilonPositive
  have halfPositive := ENNReal.half_pos epsilonPositive.ne'
  have quarterPositive := ENNReal.half_pos halfPositive.ne'
  obtain ⟨age, large, small⟩ := ((eventually_ge_atTop start).and
    (ENNReal.tendsto_nhds_zero.mp meshConvergence (epsilon / 2 / 2) quarterPositive)).exists
  obtain ⟨threshold, errors⟩ := eventually_atTop.mp
    (ENNReal.tendsto_nhds_zero.mp (errorConvergence age) (epsilon / 2) halfPositive)
  apply eventually_atTop.mpr
  refine ⟨threshold + (age + 1), fun depth beyond => ?_⟩
  have fineLarge : threshold ≤ depth - (age + 1) := by omega
  have identity : depth = (depth - (age + 1)) + (age + 1) := by omega
  calc
    distance depth = distance ((depth - (age + 1)) + (age + 1)) := congrArg distance identity
    _ ≤ mesh age + mesh age + error age (depth - (age + 1)) := bound age (by omega) _
    _ ≤ epsilon / 2 / 2 + epsilon / 2 / 2 + epsilon / 2 :=
      add_le_add (add_le_add small small) (errors _ fineLarge)
    _ = epsilon := by rw [ENNReal.add_halves, ENNReal.add_halves]

end IGSIII34.Diffusion
