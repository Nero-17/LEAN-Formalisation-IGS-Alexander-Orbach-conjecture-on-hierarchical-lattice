import IGSIII.Chemical.SubstitutionPaths.Potential

/-!
# Distance to the planted boundary in an open cell

Graph distance is zero between disconnected vertices in Lean. We therefore
minimize only over reachable planted terminals. A component touching neither
terminal has boundary height zero and is irrelevant to a planted cluster.
This also handles the one-sided components of a noncrossing cell.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

variable {Vertex : Type*} (graph : SimpleGraph Vertex)

noncomputable def componentBoundaryDistance (source target point : Vertex) : ℝ := by
  classical
  exact if graph.Reachable source point then
    if graph.Reachable target point then
      min (graph.dist source point : ℝ) (graph.dist target point : ℝ)
    else (graph.dist source point : ℝ)
  else if graph.Reachable target point then (graph.dist target point : ℝ) else 0

theorem componentBoundaryDistance_nonneg (source target point : Vertex) :
    0 ≤ componentBoundaryDistance graph source target point := by
  classical
  unfold componentBoundaryDistance
  split_ifs <;> positivity

@[simp] theorem componentBoundaryDistance_source (source target : Vertex) :
    componentBoundaryDistance graph source target source = 0 := by
  classical
  simp [componentBoundaryDistance, Nat.cast_nonneg]

@[simp] theorem componentBoundaryDistance_target (source target : Vertex) :
    componentBoundaryDistance graph source target target = 0 := by
  classical
  by_cases reachable : graph.Reachable source target <;>
    simp [componentBoundaryDistance, reachable, Nat.cast_nonneg]

theorem componentBoundaryDistance_adj_le (source target : Vertex)
    {first second : Vertex} (adjacent : graph.Adj first second) :
    componentBoundaryDistance graph source target first ≤
      componentBoundaryDistance graph source target second + 1 := by
  classical
  have sourceReach := reachable_adj_iff graph adjacent source
  have targetReach := reachable_adj_iff graph adjacent target
  have sourceBound := distance_adj_le graph adjacent source
  have targetBound := distance_adj_le graph adjacent target
  by_cases firstSource : graph.Reachable source first <;>
    by_cases firstTarget : graph.Reachable target first
  · have secondSource := sourceReach.mp firstSource
    have secondTarget := targetReach.mp firstTarget
    simp only [componentBoundaryDistance, if_pos firstSource, if_pos firstTarget,
      if_pos secondSource, if_pos secondTarget]
    calc
      min (graph.dist source first : ℝ) (graph.dist target first : ℝ) ≤
          min ((graph.dist source second : ℝ) + 1) ((graph.dist target second : ℝ) + 1) :=
        min_le_min sourceBound targetBound
      _ = _ := min_add_add_right _ _ _
  · have secondSource := sourceReach.mp firstSource
    have secondTarget : ¬graph.Reachable target second := fun reached => firstTarget (targetReach.mpr reached)
    simpa [componentBoundaryDistance, firstSource, firstTarget, secondSource, secondTarget] using sourceBound
  · have secondSource : ¬graph.Reachable source second := fun reached => firstSource (sourceReach.mpr reached)
    have secondTarget := targetReach.mp firstTarget
    simpa [componentBoundaryDistance, firstSource, firstTarget, secondSource, secondTarget] using targetBound
  · have secondSource : ¬graph.Reachable source second := fun reached => firstSource (sourceReach.mpr reached)
    have secondTarget : ¬graph.Reachable target second := fun reached => firstTarget (targetReach.mpr reached)
    simp [componentBoundaryDistance, firstSource, firstTarget, secondSource, secondTarget]

theorem componentBoundaryDistance_adj (source target : Vertex)
    {first second : Vertex} (adjacent : graph.Adj first second) :
    |componentBoundaryDistance graph source target first -
      componentBoundaryDistance graph source target second| ≤ 1 := by
  have forward := componentBoundaryDistance_adj_le graph source target adjacent
  have backward := componentBoundaryDistance_adj_le graph source target adjacent.symm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem componentBoundaryDistance_pos (source target point : Vertex)
    (notSource : point ≠ source) (notTarget : point ≠ target)
    (anchored : graph.Reachable source point ∨ graph.Reachable target point) :
    0 < componentBoundaryDistance graph source target point := by
  classical
  have sourcePositive (reached : graph.Reachable source point) :
      0 < (graph.dist source point : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun zero => notSource (reached.dist_eq_zero_iff.mp zero).symm)
  have targetPositive (reached : graph.Reachable target point) :
      0 < (graph.dist target point : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun zero => notTarget (reached.dist_eq_zero_iff.mp zero).symm)
  by_cases sourceReached : graph.Reachable source point <;>
    by_cases targetReached : graph.Reachable target point
  · simp only [componentBoundaryDistance, if_pos sourceReached, if_pos targetReached]
    exact lt_min (sourcePositive sourceReached) (targetPositive targetReached)
  · simpa [componentBoundaryDistance, sourceReached, targetReached] using sourcePositive sourceReached
  · simpa [componentBoundaryDistance, sourceReached, targetReached] using targetPositive targetReached
  · exact False.elim (anchored.elim sourceReached targetReached)

end IGSIII.Chemical.Substitution
