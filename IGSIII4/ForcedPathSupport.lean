import IGSIII4.ForcedPathStep

set_option autoImplicit false

namespace IGSIII4

theorem forced_path_step_support {Vertex : Type*} {graph : SimpleGraph Vertex}
    {current previous next terminal : Vertex} {support : List Vertex}
    (distinct : current ≠ terminal)
    (neighbors : ∀ vertex, graph.Adj current vertex → vertex = previous ∨ vertex = next)
    (tailSupport : ∀ walk : graph.Walk next terminal,
      walk.IsPath → current ∉ walk.support → walk.support = support)
    (walk : graph.Walk current terminal) (path : walk.IsPath) (avoids : previous ∉ walk.support) :
    walk.support = current :: support := by
  cases walk with
  | nil => exact (distinct rfl).elim
  | @cons start neighbor terminal adjacent tail =>
    rcases neighbors neighbor adjacent with rfl | rfl
    · exact (avoids (by simp)).elim
    · rw [SimpleGraph.Walk.support_cons, tailSupport tail path.of_cons
        (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]

end IGSIII4
