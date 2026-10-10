import IGSIII34.Diffusion.FiniteClocks
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Deterministic consequences of count limits and continuous-path convergence.
These are reusable clock lemmas; neither a Hunt process nor a Skorokhod weak
convergence theorem is assumed or asserted in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

theorem deterministic_clock_ratio (count : ℕ → ℝ) (growth resistance factor limit : ℝ)
    (growthPositive : 0 < growth) (resistanceNonzero : resistance ≠ 0)
    (factorPositive : 0 < factor) (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => count depth / growth ^ depth) atTop (𝓝 limit)) :
    Tendsto (fun depth => (growth * resistance) ^ depth /
      (factor * count depth * resistance ^ depth)) atTop (𝓝 (1 / (factor * limit))) := by
  have reciprocal := (tendsto_const_nhds (x := (1 : ℝ))).div (convergence.const_mul factor)
    (mul_pos factorPositive limitPositive).ne'
  convert reciprocal using 1
  ext depth
  dsimp only [Pi.div_apply]
  rw [mul_pow]
  field_simp [growthPositive.ne', resistanceNonzero, factorPositive.ne']

theorem degree_deterministic_clock_ratio (edgeCount : ℕ → ℝ) (growth resistance limit : ℝ)
    (growthPositive : 0 < growth) (resistanceNonzero : resistance ≠ 0)
    (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => edgeCount depth / growth ^ depth) atTop (𝓝 limit)) :
    Tendsto (fun depth => (growth * resistance) ^ depth /
      (2 * edgeCount depth * resistance ^ depth)) atTop (𝓝 (1 / (2 * limit))) :=
  deterministic_clock_ratio edgeCount growth resistance 2 limit growthPositive resistanceNonzero
    (by norm_num) limitPositive convergence

theorem counting_deterministic_clock_ratio (vertexCount : ℕ → ℝ) (growth resistance limit : ℝ)
    (growthPositive : 0 < growth) (resistanceNonzero : resistance ≠ 0)
    (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => vertexCount depth / growth ^ depth) atTop (𝓝 limit)) :
    Tendsto (fun depth => (growth * resistance) ^ depth /
      (vertexCount depth * resistance ^ depth)) atTop (𝓝 (1 / limit)) := by
  simpa only [one_mul] using deterministic_clock_ratio vertexCount growth resistance 1 limit
    growthPositive resistanceNonzero zero_lt_one limitPositive convergence

/-- Multiplication of the speed weights by a positive constant divides the
generator by that constant, leaving the quadratic form unchanged. -/
theorem speed_measure_scale_energy {Vertex : Type*} [Fintype Vertex]
    (weight generator potential : Vertex → ℝ) (constant : ℝ) (positive : 0 < constant) :
    ∑ vertex, (constant * weight vertex) * (-(generator vertex / constant)) * potential vertex =
      ∑ vertex, weight vertex * (-generator vertex) * potential vertex := by
  apply Finset.sum_congr rfl
  intro vertex _
  field_simp [positive.ne']

/-- A convergent sequence of linear clock ratios is compatible with locally
uniform convergence to a continuous path. This deterministic implication is
separate from the still-required stochastic path-law convergence. -/
theorem continuous_path_linear_clock {Space : Type*} [MetricSpace Space]
    (path : ℕ → ℝ → Space) (limitPath : ℝ → Space) (clock : ℕ → ℝ) (ratio time : ℝ)
    (pathConvergence : TendstoLocallyUniformly path limitPath atTop)
    (continuous : ContinuousAt limitPath (ratio * time))
    (clockConvergence : Tendsto clock atTop (𝓝 ratio)) :
    Tendsto (fun depth => path depth (clock depth * time)) atTop (𝓝 (limitPath (ratio * time))) :=
  pathConvergence.tendsto_comp continuous (clockConvergence.mul_const time)

end
end IGSIII34.Diffusion
