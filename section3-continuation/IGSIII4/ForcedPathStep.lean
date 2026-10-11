import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace IGSIII4

theorem forced_path_step {Vertex : Type*} {graph : SimpleGraph Vertex}
    {current previous next terminal : Vertex} {length : ℕ}
    (distinct : current ≠ terminal)
    (neighbors : ∀ vertex, graph.Adj current vertex → vertex = previous ∨ vertex = next)
    (tailLength : ∀ walk : graph.Walk next terminal,
      walk.IsPath → current ∉ walk.support → walk.length = length)
    (walk : graph.Walk current terminal) (path : walk.IsPath) (avoids : previous ∉ walk.support) :
    walk.length = length + 1 := by
  cases walk with
  | nil => exact (distinct rfl).elim
  | @cons start neighbor terminal adjacent tail =>
    rcases neighbors neighbor adjacent with rfl | rfl
    · exact (avoids (by simp)).elim
    · rw [SimpleGraph.Walk.length_cons, tailLength tail path.of_cons
        (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]

end IGSIII4
