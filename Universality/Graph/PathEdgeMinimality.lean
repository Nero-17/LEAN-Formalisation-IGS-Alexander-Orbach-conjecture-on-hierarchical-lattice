import Mathlib.Combinatorics.SimpleGraph.Paths

namespace SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

/-- A simple path has no strictly smaller path between the same endpoints. -/
theorem IsPath.eq_of_edges_subset {source target : V} (path : G.Walk source target)
    (hpath : path.IsPath) (other : G.Walk source target) (hother : other.IsPath)
    (hsubset : other.edges ⊆ path.edges) : other = path := by
  induction path with
  | nil => exact (isPath_iff_nil.mp hother).eq_nil
  | @cons source next target hadj tail ih =>
    cases other with
    | nil => exact (isPath_iff_nil.mp hpath).eq_nil.symm
    | @cons _ next' _ hadj' rest =>
      have hnext : next' = next := by
        simpa using hpath.eq_snd_of_mem_edges (w := next') (hsubset (by simp))
      subst next'
      have htail : rest.edges ⊆ tail.edges := by
        intro edge hedge
        have hmem := hsubset (List.mem_cons_of_mem _ hedge)
        rcases List.mem_cons.mp hmem with heq | hmem
        · have hnodup := hother.isTrail.edges_nodup
          rw [edges_cons, List.nodup_cons] at hnodup
          change edge = s(source, next) at heq
          exact False.elim (hnodup.1 (by simpa only [heq] using hedge))
        · exact hmem
      have heq := ih hpath.of_cons rest hother.of_cons htail
      subst rest
      rfl

end SimpleGraph.Walk
