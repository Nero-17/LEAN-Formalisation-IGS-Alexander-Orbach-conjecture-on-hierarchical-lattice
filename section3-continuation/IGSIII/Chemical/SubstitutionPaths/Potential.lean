import IGSIII.Chemical.GraphPaths

set_option autoImplicit false

/-!
# Extending terminal potentials inside an actual graph

The construction below treats disconnected cells explicitly. If both terminals
are connected, the minimum of the two distance cones extends their prescribed
values. Otherwise each terminal component receives its own constant value.
No distance identity for a substituted graph is assumed.
-/

namespace IGSIII.Chemical.Substitution

variable {Vertex : Type*} (graph : SimpleGraph Vertex)

noncomputable def terminalExtension (source target : Vertex)
    (sourceValue targetValue : ℝ) (vertex : Vertex) : ℝ := by
  classical
  exact if graph.Reachable source vertex then
    if graph.Reachable source target then
      min (sourceValue + (graph.dist source vertex : ℝ))
        (targetValue + (graph.dist target vertex : ℝ))
    else sourceValue
  else if graph.Reachable target vertex then targetValue else 0

theorem terminalExtension_source (source target : Vertex)
    (sourceValue targetValue : ℝ)
    (boundaryBound : graph.Reachable source target →
      |sourceValue - targetValue| ≤ (graph.dist source target : ℝ)) :
    terminalExtension graph source target sourceValue targetValue source = sourceValue := by
  classical
  by_cases crossing : graph.Reachable source target
  · have bound := (abs_le.mp (boundaryBound crossing)).2
    simp only [terminalExtension, if_pos (SimpleGraph.Reachable.refl source),
      if_pos crossing, SimpleGraph.dist_self, Nat.cast_zero, add_zero]
    rw [SimpleGraph.dist_comm]
    apply min_eq_left
    linarith
  · simp [terminalExtension, crossing]

theorem terminalExtension_target (source target : Vertex)
    (sourceValue targetValue : ℝ)
    (boundaryBound : graph.Reachable source target →
      |sourceValue - targetValue| ≤ (graph.dist source target : ℝ)) :
    terminalExtension graph source target sourceValue targetValue target = targetValue := by
  classical
  by_cases crossing : graph.Reachable source target
  · have bound := (abs_le.mp (boundaryBound crossing)).1
    simp only [terminalExtension, if_pos crossing, SimpleGraph.dist_self,
      Nat.cast_zero, add_zero]
    apply min_eq_right
    linarith
  · simp [terminalExtension, crossing]

theorem reachable_adj_iff {first second : Vertex} (adjacent : graph.Adj first second)
    (root : Vertex) : graph.Reachable root first ↔ graph.Reachable root second :=
  ⟨fun reachable => reachable.trans adjacent.reachable,
    fun reachable => reachable.trans adjacent.symm.reachable⟩

theorem distance_adj_le {first second : Vertex} (adjacent : graph.Adj first second)
    (root : Vertex) : (graph.dist root first : ℝ) ≤ (graph.dist root second : ℝ) + 1 := by
  have bound := adjacent.symm.reachable.dist_triangle_right root
  have length : graph.dist second first = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr adjacent.symm
  rw [length] at bound
  exact_mod_cast bound

theorem terminalExtension_adj_le (source target : Vertex)
    (sourceValue targetValue : ℝ) {first second : Vertex}
    (adjacent : graph.Adj first second) :
    terminalExtension graph source target sourceValue targetValue first ≤
      terminalExtension graph source target sourceValue targetValue second + 1 := by
  classical
  have sourceReach := reachable_adj_iff graph adjacent source
  have targetReach := reachable_adj_iff graph adjacent target
  by_cases firstSource : graph.Reachable source first
  · have secondSource := sourceReach.mp firstSource
    by_cases crossing : graph.Reachable source target
    · simp only [terminalExtension, if_pos firstSource, if_pos secondSource, if_pos crossing]
      have firstBound := distance_adj_le graph adjacent source
      have secondBound := distance_adj_le graph adjacent target
      calc
        min (sourceValue + (graph.dist source first : ℝ))
            (targetValue + (graph.dist target first : ℝ)) ≤
            min ((sourceValue + (graph.dist source second : ℝ)) + 1)
              ((targetValue + (graph.dist target second : ℝ)) + 1) :=
          min_le_min (by linarith) (by linarith)
        _ = _ := min_add_add_right _ _ _
    · simp [terminalExtension, firstSource, secondSource, crossing]
  · have secondSource : ¬ graph.Reachable source second := fun reachable =>
      firstSource (sourceReach.mpr reachable)
    by_cases firstTarget : graph.Reachable target first
    · have secondTarget := targetReach.mp firstTarget
      simp [terminalExtension, firstSource, secondSource, firstTarget, secondTarget]
    · have secondTarget : ¬ graph.Reachable target second := fun reachable =>
        firstTarget (targetReach.mpr reachable)
      simp [terminalExtension, firstSource, secondSource, firstTarget, secondTarget]

theorem terminalExtension_adj_bound (source target : Vertex)
    (sourceValue targetValue : ℝ) {first second : Vertex}
    (adjacent : graph.Adj first second) :
    |terminalExtension graph source target sourceValue targetValue first -
      terminalExtension graph source target sourceValue targetValue second| ≤ 1 := by
  have forward := terminalExtension_adj_le graph source target sourceValue targetValue adjacent
  have backward := terminalExtension_adj_le graph source target sourceValue targetValue adjacent.symm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem potential_difference_le_walk_length (potential : Vertex → ℝ)
    (edgeBound : ∀ {first second}, graph.Adj first second →
      |potential first - potential second| ≤ 1)
    {source target : Vertex} (walk : graph.Walk source target) :
    |potential source - potential target| ≤ (walk.length : ℝ) := by
  induction walk with
  | nil => simp
  | @cons first second last adjacent rest inductionHypothesis =>
      calc
        |potential first - potential last| ≤
            |potential first - potential second| + |potential second - potential last| :=
          abs_sub_le _ _ _
        _ ≤ 1 + (rest.length : ℝ) := add_le_add (edgeBound adjacent) inductionHypothesis
        _ = ((SimpleGraph.Walk.cons adjacent rest).length : ℝ) := by
          simp [add_comm]

end IGSIII.Chemical.Substitution
