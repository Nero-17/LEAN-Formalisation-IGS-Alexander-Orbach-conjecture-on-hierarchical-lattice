import IGSIII34.Diffusion.FiniteGreedyExitProbabilityCompletion20261011
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem finite_increasing_partition_index_completion20261011
    (times : ℕ → ℕ) (zero : times 0 = 0) (steps time : ℕ) (lastAfter : time < times steps) :
    ∃ step, step < steps ∧ times step ≤ time ∧ time < times (step + 1) := by
  classical
  let step := Nat.findGreatest (fun step => times step ≤ time) steps
  have stepBound : step ≤ steps := Nat.findGreatest_le steps
  have startBefore : times step ≤ time := by
    by_cases equal : step = 0
    · simp only [equal, zero, Nat.zero_le]
    · exact Nat.findGreatest_of_ne_zero (P := fun step => times step ≤ time) rfl equal
  have strict : step < steps := by
    by_contra failure
    have equal : step = steps := by omega
    rw [equal] at startBefore
    omega
  have nextAfter : time < times (step + 1) := by
    exact not_le.mp (Nat.findGreatest_is_greatest (P := fun step => times step ≤ time)
      (n := steps) (show step < step + 1 by omega) (by omega))
  exact ⟨step, strict, startBefore, nextAfter⟩

theorem partition_long_gaps_modulus_completion20261011
    {Carrier : Type*} [MetricSpace Carrier] (path : ℕ → Carrier)
    (times : ℕ → ℕ) (zero : times 0 = 0) (ordered : Monotone times)
    (steps horizon window : ℕ) (lastAfter : horizon < times steps)
    (radius jump : ℝ) (radiusNonnegative : 0 ≤ radius) (jumpNonnegative : 0 ≤ jump)
    (beforeExit : ∀ step < steps, ∀ index, times step ≤ index → index < times (step + 1) →
      dist (path (times step)) (path index) < radius)
    (exitJump : ∀ step < steps, times (step + 1) ≤ horizon →
      dist (path (times step)) (path (times (step + 1))) ≤ radius + jump)
    (longGaps : ∀ step < steps, times (step + 1) ≤ horizon →
      times step + window < times (step + 1))
    (first last : ℕ) (orderedWindow : first ≤ last) (beforeHorizon : last ≤ horizon)
    (smallWindow : last ≤ first + window) :
    dist (path first) (path last) ≤ 3 * radius + jump := by
  obtain ⟨start, startBound, startBefore, startAfter⟩ := finite_increasing_partition_index_completion20261011
    times zero steps first (by omega)
  obtain ⟨finish, finishBound, finishBefore, finishAfter⟩ := finite_increasing_partition_index_completion20261011
    times zero steps last (by omega)
  have startFinish : start ≤ finish := by
    by_contra failure
    have chronological := ordered (show finish + 1 ≤ start by omega)
    omega
  have atMostOne : finish ≤ start + 1 := by
    by_contra failure
    have chronological := ordered (show start + 1 + 1 ≤ finish by omega)
    have long := longGaps (start + 1) (by omega) (chronological.trans (finishBefore.trans beforeHorizon))
    omega
  have firstClose : dist (path first) (path (times start)) < radius := by
    rw [dist_comm]
    exact beforeExit start startBound first startBefore startAfter
  have lastClose := beforeExit finish finishBound last finishBefore finishAfter
  by_cases same : finish = start
  · rw [same] at lastClose
    have triangle := dist_triangle (path first) (path (times start)) (path last)
    linarith
  · have next : finish = start + 1 := by omega
    have middleBefore : times (start + 1) ≤ horizon := by
      simpa only [next] using finishBefore.trans beforeHorizon
    have middle := exitJump start startBound middleBefore
    have triangle := dist_triangle (path first) (path (times start)) (path last)
    have otherTriangle := dist_triangle (path (times start)) (path (times finish)) (path last)
    rw [next] at otherTriangle lastClose
    linarith

variable {Vertex Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [MetricSpace Carrier]

theorem finiteGreedyExitNext_jump_completion20261011
    (embedding : Vertex → Carrier) (radius : ℝ) (radiusPositive : 0 < radius)
    (horizon : ℕ) (first : (ℕ → Vertex) → ℕ) (bounded : ∀ path, first path ≤ horizon + 1)
    (path : ℕ → Vertex) (jump : ℝ)
    (jumpBound : ∀ index < horizon, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump)
    (actualExit : finiteGreedyExitNextCompletion20261011 embedding radius horizon first path ≤ horizon) :
    dist (embedding (path (first path)))
      (embedding (path (finiteGreedyExitNextCompletion20261011 embedding radius horizon first path))) ≤ radius + jump := by
  let next := finiteGreedyExitNextCompletion20261011 embedding radius horizon first path
  have startBefore := (finiteGreedyExitNext_bound_completion20261011 embedding radius horizon first bounded path).1
  have strict : first path < next := by
    have hit := finiteGreedyExitNext_hit_completion20261011 embedding radius horizon first path actualExit
    by_contra failure
    have equal : first path = next := by omega
    change radius ≤ dist (embedding (path (first path))) (embedding (path next)) at hit
    rw [← equal, dist_self] at hit
    linarith
  have nextPositive : 0 < next := by omega
  have prevAfter : first path ≤ next - 1 := by omega
  have prevBefore : next - 1 < next := by omega
  have near := finiteGreedyExitNext_before_completion20261011 embedding radius horizon first path (next - 1) prevAfter prevBefore
  have jumpBoundHere := jumpBound (next - 1) (by omega)
  have successor : next - 1 + 1 = next := by omega
  rw [successor] at jumpBoundHere
  have triangle := dist_triangle (embedding (path (first path))) (embedding (path (next - 1))) (embedding (path next))
  linarith

/-- Deterministic small-window control of the actual embedded greedy path.
The long-gap event and the actual one-step jump bound replace any assumed
path-tightness or path-regularity assertion. -/
theorem finiteGreedyExitTime_modulus_completion20261011
    (embedding : Vertex → Carrier) (radius : ℝ) (radiusPositive : 0 < radius)
    (steps horizon window : ℕ) (path : ℕ → Vertex) (jump : ℝ) (jumpNonnegative : 0 ≤ jump)
    (jumpBound : ∀ index < horizon, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump)
    (lastAfter : horizon < finiteGreedyExitTimeCompletion20261011 embedding radius horizon steps path)
    (noShort : ∀ step < steps, path ∉ finiteGreedyShortGapCompletion20261011 embedding radius horizon window step)
    (first last : ℕ) (orderedWindow : first ≤ last) (beforeHorizon : last ≤ horizon)
    (smallWindow : last ≤ first + window) :
    dist (embedding (path first)) (embedding (path last)) ≤ 3 * radius + jump := by
  have monotone : Monotone (fun step => finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path) :=
    monotone_nat_of_le_succ fun step =>
      (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step).2.2 path
  exact partition_long_gaps_modulus_completion20261011 (fun index => embedding (path index))
    (fun step => finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path) rfl monotone
    steps horizon window lastAfter radius jump radiusPositive.le jumpNonnegative
    (fun step _ index after before => finiteGreedyExitNext_before_completion20261011 embedding radius horizon
      (finiteGreedyExitTimeCompletion20261011 embedding radius horizon step) path index after before)
    (fun step _ actualExit => finiteGreedyExitNext_jump_completion20261011 embedding radius radiusPositive horizon
      (finiteGreedyExitTimeCompletion20261011 embedding radius horizon step)
      (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step).2.1 path jump jumpBound actualExit)
    (fun step before actualExit => by
      have notShort := noShort step before
      exact not_le.mp (fun short => notShort ⟨actualExit, short⟩))
    first last orderedWindow beforeHorizon smallWindow

end
end IGSIII34.Diffusion
