import IGSIII.Chemical.WeightedGraphMetric
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuity of the finite chemical skeleton

Every shortest-path distance in a fixed finite graph converges when its edge
costs converge. This is the finite-skeleton continuity step in `thm:full-ghp`.
-/

set_option autoImplicit false

namespace IGSIII.Geometry

open Filter IGSIII.Chemical
open scoped Topology

variable {Edge : Type*} [DecidableEq Edge] [Fintype Edge]

theorem shortest_tendsto (family : PathFamily Edge)
    (costs : ℕ → Edge → ℝ) (limitCost : Edge → ℝ)
    (converges : ∀ edge, Tendsto (fun depth => costs depth edge) atTop (𝓝 (limitCost edge))) :
    Tendsto (fun depth => family.shortest (costs depth)) atTop (𝓝 (family.shortest limitCost)) := by
  have errorsConverge : Tendsto
      (fun depth => ∑ edge, |costs depth edge - limitCost edge|) atTop (𝓝 0) := by
    have each : ∀ edge, Tendsto (fun depth => |costs depth edge - limitCost edge|) atTop (𝓝 0) := by
      intro edge
      simpa using ((converges edge).sub_const (limitCost edge)).abs
    simpa using tendsto_finsetSum Finset.univ (fun edge _ => each edge)
  apply Metric.tendsto_atTop.mpr
  intro epsilon positive
  obtain ⟨start, small⟩ := eventually_atTop.mp ((tendsto_order.mp errorsConverge).2 epsilon positive)
  refine ⟨start, fun depth beyond => ?_⟩
  rw [Real.dist_eq]
  exact (family.shortest_lipschitz (costs depth) limitCost).trans_lt (small depth beyond)

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem weightedDistance_tendsto (graph : SimpleGraph Vertex)
    (costs : ℕ → Sym2 Vertex → ℝ) (limitCost : Sym2 Vertex → ℝ)
    (converges : ∀ edge, Tendsto (fun depth => costs depth edge) atTop (𝓝 (limitCost edge)))
    (source target : Vertex) :
    Tendsto (fun depth => Chemical.Substitution.weightedDistance graph (costs depth) source target)
      atTop (𝓝 (Chemical.Substitution.weightedDistance graph limitCost source target)) := by
  classical
  by_cases reachable : graph.Reachable source target
  · simp_rw [Chemical.Substitution.weightedDistance_of_reachable graph _ reachable]
    exact shortest_tendsto (graphPathFamily graph source target reachable) costs limitCost converges
  · simp only [Chemical.Substitution.weightedDistance, dif_neg reachable]
    exact tendsto_const_nhds

end IGSIII.Geometry
