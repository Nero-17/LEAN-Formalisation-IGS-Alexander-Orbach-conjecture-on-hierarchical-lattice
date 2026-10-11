import Universality.Geometry.CompactCellTree
import Mathlib.Data.Set.Finite.Lattice

namespace Universality.Geometry
open Set

/-- Intersecting the finite-level recursion gives the graph-directed set
equation. This is pathwise: a whole first-rule family is held fixed, and each
child may have its own subsequent random rule choices. -/
theorem graphDirected_limit_equation {X : Type*} {Edge : Type*} [Finite Edge]
    (ChildSpace : Edge → Type*) (map : (e : Edge) → ChildSpace e → X)
    (hinjective : ∀ e, Function.Injective (map e))
    (childLevel : (e : Edge) → ℕ → Set (ChildSpace e))
    (hnested : ∀ e, Antitone (childLevel e))
    (rootLevel : ℕ → Set X)
    (hrecursion : ∀ n, rootLevel (n + 1) = ⋃ e, map e '' childLevel e n)
    (hfirst : rootLevel 1 ⊆ rootLevel 0) :
    (⋂ n, rootLevel n) = ⋃ e, map e '' (⋂ n, childLevel e n) := by
  have hshift : (⋂ n, rootLevel n) = ⋂ n, rootLevel (n + 1) := by
    ext x
    simp only [mem_iInter]
    constructor
    · exact fun h n => h (n + 1)
    · intro h n
      cases n with
      | zero => exact hfirst (h 0)
      | succ n => exact h n
  rw [hshift]
  simp_rw [hrecursion]
  rw [Set.iInter_iUnion_of_antitone (s := fun e n => map e '' childLevel e n)
    (fun e i j hij => image_mono (hnested e hij))]
  congr 1
  funext e
  exact ((hinjective e).injOn.image_iInter_eq).symm

end Universality.Geometry
