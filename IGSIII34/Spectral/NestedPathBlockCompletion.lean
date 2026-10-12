import IGSIII34.Spectral.ActualDescendantAnchorCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace IGSIII34.Spectral
noncomputable section
open scoped Topology

theorem nested_path_castLE_completion {Entry : Type*}
    (path : Π depth, Fin depth → Entry) (nested : ∀ depth, Fin.init (path (depth + 1)) = path depth)
    (first second : ℕ) (bound : first ≤ second) (index : Fin first) :
    path second (Fin.castLE bound index) = path first index := by
  induction second, bound using Nat.le_induction with
  | base => rfl
  | succ second bound hypothesis =>
      have next := congrFun (nested second) (Fin.castLE bound index)
      exact next.trans hypothesis

theorem nested_path_block_decomposition_completion {Entry : Type*}
    (path : Π depth, Fin depth → Entry) (nested : ∀ depth, Fin.init (path (depth + 1)) = path depth)
    (coarse fine : ℕ) :
    ∃ suffix : Fin (fine + 1) → Entry,
      path (coarse + fine + 2) = blockWordAppendCompletion coarse fine (path (coarse + 1)) suffix := by
  let suffix : Fin (fine + 1) → Entry :=
    fun index => path (coarse + fine + 2) ⟨coarse + 1 + index.val, by omega⟩
  refine ⟨suffix, ?_⟩
  have decomposition (index : Fin ((coarse + 1) + (fine + 1))) :
      path (coarse + fine + 2) (Fin.cast (by omega) index) = Fin.append (path (coarse + 1)) suffix index := by
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · rw [Fin.append_left]
      exact nested_path_castLE_completion path nested (coarse + 1) (coarse + fine + 2) (by omega) index
    · rw [Fin.append_right]
      rfl
  funext index
  exact decomposition (Fin.cast (by omega) index)

end
end IGSIII34.Spectral
