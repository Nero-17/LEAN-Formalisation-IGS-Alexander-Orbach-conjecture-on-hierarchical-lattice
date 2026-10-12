import IGSIII.Geometry.CellLocalisationCone
import Universality.Graph.InternalCellNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII.Geometry
noncomputable section
open IGSIII.Chemical.Substitution

/-- The four boundary routes, including the route that stays inside. Repeated
boundary points cover components with only one planted boundary. -/
def twoBoundaryRouteDistance {Local Ambient : Type*}
    [PseudoMetricSpace Local] [PseudoMetricSpace Ambient]
    (inclusion : Local → Ambient) (boundary : Bool → Local) (first last : Local) : ℝ :=
  min (dist first last)
    (min
      (min (dist first (boundary false) + dist (inclusion (boundary false)) (inclusion (boundary false)) + dist (boundary false) last)
        (dist first (boundary false) + dist (inclusion (boundary false)) (inclusion (boundary true)) + dist (boundary true) last))
      (min (dist first (boundary true) + dist (inclusion (boundary true)) (inclusion (boundary false)) + dist (boundary false) last)
        (dist first (boundary true) + dist (inclusion (boundary true)) (inclusion (boundary true)) + dist (boundary true) last)))

theorem twoBoundaryRouteDistance_le_direct {Local Ambient : Type*}
    [PseudoMetricSpace Local] [PseudoMetricSpace Ambient]
    (inclusion : Local → Ambient) (boundary : Bool → Local) (first last : Local) :
    twoBoundaryRouteDistance inclusion boundary first last ≤ dist first last :=
  min_le_left _ _

theorem twoBoundaryRouteDistance_le_route {Local Ambient : Type*}
    [PseudoMetricSpace Local] [PseudoMetricSpace Ambient]
    (inclusion : Local → Ambient) (boundary : Bool → Local) (first last : Local)
    (exit entrance : Bool) :
    twoBoundaryRouteDistance inclusion boundary first last ≤
      dist first (boundary exit) + dist (inclusion (boundary exit)) (inclusion (boundary entrance)) + dist (boundary entrance) last := by
  cases exit <;> cases entrance
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- A genuine first-exit decomposition of every ambient walk. Until the first
boundary vertex, every edge lifts into the intrinsic component. -/
theorem weighted_walk_first_exit {Local Ambient : Type*}
    [PseudoMetricSpace Local] [Fintype Ambient] [DecidableEq Ambient]
    (graph : SimpleGraph Ambient) (cost : Sym2 Ambient → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond) (inclusion : Local → Ambient)
    (boundary : Bool → Local)
    (internalNeighbor : ∀ point : Local, (∀ side, point ≠ boundary side) →
      ∀ neighbor : Ambient, graph.Adj (inclusion point) neighbor →
      ∃ inside : Local, inclusion inside = neighbor ∧
        dist point inside ≤ cost s(inclusion point, neighbor))
    {start last : Ambient} (walk : graph.Walk start last) (first : Local)
    (startIdentity : inclusion first = start) :
    (∃ inside : Local, inclusion inside = last ∧ dist first inside ≤ (walk.edges.map cost).sum) ∨
      ∃ side : Bool, dist first (boundary side) +
        weightedDistance graph cost (inclusion (boundary side)) last ≤ (walk.edges.map cost).sum := by
  classical
  induction walk generalizing first with
  | nil =>
    exact Or.inl ⟨first, startIdentity, by simp⟩
  | @cons start next last adjacent rest inductionHypothesis =>
    by_cases atBoundary : ∃ side, first = boundary side
    · obtain ⟨side, rfl⟩ := atBoundary
      refine Or.inr ⟨side, ?_⟩
      simpa only [startIdentity, dist_self, zero_add] using
        weightedDistance_le_walkCost graph cost nonnegative (SimpleGraph.Walk.cons adjacent rest)
    · have interior : ∀ side, first ≠ boundary side := by
        intro side same
        exact atBoundary ⟨side, same⟩
      obtain ⟨inside, insideIdentity, stepBound⟩ :=
        internalNeighbor first interior next (by simpa only [startIdentity] using adjacent)
      rcases inductionHypothesis inside insideIdentity with ⟨target, targetIdentity, tailBound⟩ | ⟨side, tailBound⟩
      · refine Or.inl ⟨target, targetIdentity, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
        rw [startIdentity] at stepBound
        exact (dist_triangle first inside target).trans (add_le_add stepBound tailBound)
      · refine Or.inr ⟨side, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
        rw [startIdentity] at stepBound
        have triangle := dist_triangle first inside (boundary side)
        linarith

/-- Exact finite-graph first-exit/last-entrance identity. The assumptions are
edgewise local lifting and the actual ambient weighted graph metric. -/
theorem weighted_graph_two_boundary_route_equality {Local Ambient : Type*}
    [PseudoMetricSpace Local] [PseudoMetricSpace Ambient]
    [Fintype Ambient] [DecidableEq Ambient]
    (graph : SimpleGraph Ambient) (cost : Sym2 Ambient → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    (ambientDistance : ∀ first last, graph.Reachable first last →
      dist first last = weightedDistance graph cost first last)
    (inclusion : Local → Ambient) (injective : Function.Injective inclusion)
    (contractive : ∀ first last, dist (inclusion first) (inclusion last) ≤ dist first last)
    (reachable : ∀ first last : Local, graph.Reachable (inclusion first) (inclusion last))
    (boundary : Bool → Local)
    (internalNeighbor : ∀ point : Local, (∀ side, point ≠ boundary side) →
      ∀ neighbor : Ambient, graph.Adj (inclusion point) neighbor →
      ∃ inside : Local, inclusion inside = neighbor ∧
        dist point inside ≤ cost s(inclusion point, neighbor))
    (first last : Local) :
    dist (inclusion first) (inclusion last) =
      twoBoundaryRouteDistance inclusion boundary first last := by
  apply le_antisymm
  · have routeBound (exit entrance : Bool) :
        dist (inclusion first) (inclusion last) ≤
          dist first (boundary exit) + dist (inclusion (boundary exit)) (inclusion (boundary entrance)) + dist (boundary entrance) last := by
      calc
        dist (inclusion first) (inclusion last) ≤
            dist (inclusion first) (inclusion (boundary entrance)) + dist (inclusion (boundary entrance)) (inclusion last) :=
          dist_triangle _ _ _
        _ ≤ (dist (inclusion first) (inclusion (boundary exit)) +
              dist (inclusion (boundary exit)) (inclusion (boundary entrance))) + dist (inclusion (boundary entrance)) (inclusion last) :=
          add_le_add (dist_triangle _ _ _) (le_refl _)
        _ ≤ (dist first (boundary exit) +
              dist (inclusion (boundary exit)) (inclusion (boundary entrance))) + dist (boundary entrance) last :=
          add_le_add (add_le_add (contractive _ _) (le_refl _)) (contractive _ _)
    exact le_min (contractive first last)
      (le_min (le_min (routeBound false false) (routeBound false true))
        (le_min (routeBound true false) (routeBound true true)))
  · obtain ⟨walk, _, minimizing⟩ := exists_weighted_geodesic graph cost (reachable first last)
    rcases weighted_walk_first_exit graph cost nonnegative inclusion boundary internalNeighbor walk first rfl with
      ⟨inside, insideIdentity, insideBound⟩ | ⟨exit, exitBound⟩
    · have same : inside = last := injective insideIdentity
      subst inside
      rw [minimizing, ← ambientDistance _ _ (reachable first last)] at insideBound
      exact (twoBoundaryRouteDistance_le_direct inclusion boundary first last).trans insideBound
    · rw [minimizing, ← ambientDistance _ _ (reachable first last),
        ← ambientDistance _ _ (reachable (boundary exit) last)] at exitBound
      obtain ⟨reverseWalk, _, reverseMinimizing⟩ := exists_weighted_geodesic graph cost (reachable last (boundary exit))
      rcases weighted_walk_first_exit graph cost nonnegative inclusion boundary internalNeighbor reverseWalk last rfl with
        ⟨inside, insideIdentity, insideBound⟩ | ⟨entrance, entranceBound⟩
      · have same : inside = boundary exit := injective insideIdentity
        subst inside
        rw [reverseMinimizing, ← ambientDistance _ _ (reachable last (boundary exit)), dist_comm last] at insideBound
        have routeBound := twoBoundaryRouteDistance_le_route inclusion boundary first last exit exit
        simp only [dist_self, add_zero] at routeBound
        rw [dist_comm (boundary exit) last] at routeBound
        exact routeBound.trans (by linarith [dist_comm (inclusion last) (inclusion (boundary exit)), dist_comm last (boundary exit)])
      · rw [reverseMinimizing, ← ambientDistance _ _ (reachable last (boundary exit)),
          ← ambientDistance _ _ (reachable (boundary entrance) (boundary exit))] at entranceBound
        have routeBound := twoBoundaryRouteDistance_le_route inclusion boundary first last exit entrance
        rw [dist_comm (inclusion (boundary exit)) (inclusion (boundary entrance)), dist_comm (boundary entrance) last] at routeBound
        exact routeBound.trans (by linarith [dist_comm (inclusion last) (inclusion (boundary exit))])


/-- The route formula directly in the ambient graph distance. This does not
require a metric on ambient vertices outside the retained cluster. -/
def twoBoundaryWeightedRouteDistance {Local Ambient : Type*}
    [PseudoMetricSpace Local] [Fintype Ambient] [DecidableEq Ambient]
    (graph : SimpleGraph Ambient) (cost : Sym2 Ambient → ℝ)
    (inclusion : Local → Ambient) (boundary : Bool → Local) (first last : Local) : ℝ :=
  min (dist first last)
    (min
      (min (dist first (boundary false) + weightedDistance graph cost (inclusion (boundary false)) (inclusion (boundary false)) + dist (boundary false) last)
        (dist first (boundary false) + weightedDistance graph cost (inclusion (boundary false)) (inclusion (boundary true)) + dist (boundary true) last))
      (min (dist first (boundary true) + weightedDistance graph cost (inclusion (boundary true)) (inclusion (boundary false)) + dist (boundary false) last)
        (dist first (boundary true) + weightedDistance graph cost (inclusion (boundary true)) (inclusion (boundary true)) + dist (boundary true) last)))

theorem twoBoundaryWeightedRouteDistance_le_route {Local Ambient : Type*}
    [PseudoMetricSpace Local] [Fintype Ambient] [DecidableEq Ambient]
    (graph : SimpleGraph Ambient) (cost : Sym2 Ambient → ℝ)
    (inclusion : Local → Ambient) (boundary : Bool → Local) (first last : Local)
    (exit entrance : Bool) :
    twoBoundaryWeightedRouteDistance graph cost inclusion boundary first last ≤
      dist first (boundary exit) + weightedDistance graph cost (inclusion (boundary exit)) (inclusion (boundary entrance)) + dist (boundary entrance) last := by
  cases exit <;> cases entrance
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem weighted_graph_two_boundary_route_direct_equality {Local Ambient : Type*}
    [PseudoMetricSpace Local] [Fintype Ambient] [DecidableEq Ambient]
    (graph : SimpleGraph Ambient) (cost : Sym2 Ambient → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    (inclusion : Local → Ambient) (injective : Function.Injective inclusion)
    (contractive : ∀ first last, weightedDistance graph cost (inclusion first) (inclusion last) ≤ dist first last)
    (reachable : ∀ first last : Local, graph.Reachable (inclusion first) (inclusion last))
    (boundary : Bool → Local)
    (internalNeighbor : ∀ point : Local, (∀ side, point ≠ boundary side) →
      ∀ neighbor : Ambient, graph.Adj (inclusion point) neighbor →
      ∃ inside : Local, inclusion inside = neighbor ∧
        dist point inside ≤ cost s(inclusion point, neighbor))
    (first last : Local) :
    weightedDistance graph cost (inclusion first) (inclusion last) =
      twoBoundaryWeightedRouteDistance graph cost inclusion boundary first last := by
  apply le_antisymm
  · have routeBound (exit entrance : Bool) :
        weightedDistance graph cost (inclusion first) (inclusion last) ≤
          dist first (boundary exit) + weightedDistance graph cost (inclusion (boundary exit)) (inclusion (boundary entrance)) + dist (boundary entrance) last := by
      have firstTriangle := weightedDistance_triangle graph cost nonnegative
        (reachable first (boundary entrance)) (reachable (boundary entrance) last)
      have secondTriangle := weightedDistance_triangle graph cost nonnegative
        (reachable first (boundary exit)) (reachable (boundary exit) (boundary entrance))
      have firstContraction := contractive first (boundary exit)
      have lastContraction := contractive (boundary entrance) last
      linarith
    exact le_min (contractive first last)
      (le_min (le_min (routeBound false false) (routeBound false true))
        (le_min (routeBound true false) (routeBound true true)))
  · obtain ⟨walk, _, minimizing⟩ := exists_weighted_geodesic graph cost (reachable first last)
    rcases weighted_walk_first_exit graph cost nonnegative inclusion boundary internalNeighbor walk first rfl with
      ⟨inside, insideIdentity, insideBound⟩ | ⟨exit, exitBound⟩
    · have same : inside = last := injective insideIdentity
      subst inside
      rw [minimizing] at insideBound
      exact (min_le_left _ _).trans insideBound
    · rw [minimizing] at exitBound
      obtain ⟨reverseWalk, _, reverseMinimizing⟩ := exists_weighted_geodesic graph cost (reachable last (boundary exit))
      rcases weighted_walk_first_exit graph cost nonnegative inclusion boundary internalNeighbor reverseWalk last rfl with
        ⟨inside, insideIdentity, insideBound⟩ | ⟨entrance, entranceBound⟩
      · have same : inside = boundary exit := injective insideIdentity
        subst inside
        rw [reverseMinimizing, weightedDistance_comm graph cost nonnegative (inclusion last)] at insideBound
        have routeBound := twoBoundaryWeightedRouteDistance_le_route graph cost inclusion boundary first last exit exit
        simp only [weightedDistance_self graph cost nonnegative, add_zero] at routeBound
        rw [dist_comm (boundary exit) last] at routeBound
        exact routeBound.trans (by linarith)
      · rw [reverseMinimizing,
          weightedDistance_comm graph cost nonnegative (inclusion last),
          weightedDistance_comm graph cost nonnegative (inclusion (boundary entrance))] at entranceBound
        have routeBound := twoBoundaryWeightedRouteDistance_le_route graph cost inclusion boundary first last exit entrance
        rw [dist_comm (boundary entrance) last] at routeBound
        exact routeBound.trans (by linarith)

end
end IGSIII.Geometry
