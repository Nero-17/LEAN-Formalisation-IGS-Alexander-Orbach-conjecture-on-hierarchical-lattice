import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- Genuine J1 convergence to a continuous path upgrades to uniform
convergence. The proof uses the inverse of the actual time change. -/
theorem skorokhodJ1_near_continuous_uniform_completion
    (limit : C(SkorokhodIntervalTimeCompletion, Space))
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ error : ℝ, 0 < error ∧ ∀ path : SkorokhodIntervalPathCompletion Space,
      dist path (continuousIntervalPathCompletion limit) < error →
        ∀ time, dist (path time) (limit time) < tolerance := by
  obtain ⟨duration, durationPositive, continuousClose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous limit.continuous) (tolerance / 2) (by positivity)
  let error := min duration (tolerance / 2)
  have errorPositive : 0 < error := lt_min durationPositive (by positivity)
  refine ⟨error, errorPositive, ?_⟩
  intro path near time
  have nearEDistance : skorokhodJ1EDistCompletion path (continuousIntervalPathCompletion limit) < ENNReal.ofReal error :=
    edist_lt_ofReal.mpr near
  obtain ⟨change, changeSmall⟩ := iInf_lt_iff.mp nearEDistance
  have timeSmall : ∀ next, dist (change next) next < error := by
    intro next
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (change next) next) next).trans (le_max_left _ _)).trans_lt changeSmall
  have spatialSmall : ∀ next, dist (path (change next)) (limit next) < error := by
    intro next
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (path (change next)) (limit next)) next).trans (le_max_right _ _)).trans_lt changeSmall
  have spatial := spatialSmall (change.symm time)
  rw [change.apply_symm_apply] at spatial
  have inverseTime : dist (change.symm time) time < duration := by
    have small := timeSmall (change.symm time)
    rw [change.apply_symm_apply, dist_comm] at small
    exact small.trans_le (min_le_left _ _)
  have continuousNear := continuousClose inverseTime
  have triangle := dist_triangle (path time) (limit (change.symm time)) (limit time)
  have errorBound : error ≤ tolerance / 2 := min_le_right _ _
  linarith

theorem skorokhodJ1_continuous_limit_uniform_completion
    {Index : Type*} (filter : Filter Index)
    (paths : Index → SkorokhodIntervalPathCompletion Space)
    (limit : C(SkorokhodIntervalTimeCompletion, Space))
    (convergence : Tendsto paths filter (𝓝 (continuousIntervalPathCompletion limit))) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in filter, ∀ time,
      dist (paths index time) (limit time) < tolerance := by
  intro tolerance positive
  obtain ⟨error, errorPositive, close⟩ := skorokhodJ1_near_continuous_uniform_completion limit tolerance positive
  filter_upwards [convergence.eventually (Metric.ball_mem_nhds _ errorPositive)] with index near
  exact close (paths index) near

end
end IGSIII34.Diffusion
