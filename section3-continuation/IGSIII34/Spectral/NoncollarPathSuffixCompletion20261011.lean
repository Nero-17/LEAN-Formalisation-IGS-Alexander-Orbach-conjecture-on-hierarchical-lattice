import IGSIII34.Spectral.BoundaryCollarMassCompletion20261011
import IGSIII34.Spectral.NestedPathBlockCompletion20261011
import IGSIII34.Spectral.NoncollarRootInteriorCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem actual_noncollar_path_suffix_completion20261011
    (rule : Rule) (coarseDepth collarDepth : ℕ)
    (path : Π depth, Fin depth → (Fin rule.edges × Bool))
    (parentWord : Fin coarseDepth → (Fin rule.edges × Bool))
    (edges : Fin collarDepth → Fin rule.edges) (sides : Fin collarDepth → Bool)
    (decomposition : path (coarseDepth + collarDepth) =
      Fin.append parentWord (fun index => (edges index, sides index)))
    (avoids : path ∉ terminalCylinderCollarCompletion20261011 rule 0 coarseDepth collarDepth) :
    ∀ side : Bool, edges ∉ actualTerminalSocketSetCompletion20261011 rule 0 collarDepth side := by
  intro side member
  apply avoids
  unfold terminalCylinderCollarCompletion20261011
  apply Set.mem_iUnion.mpr
  refine ⟨parentWord, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨side, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨edges, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨member, ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨sides, decomposition⟩

theorem nested_path_uncast_block_decomposition_completion20261011
    (rule : Rule) (path : Π depth, Fin depth → (Fin rule.edges × Bool))
    (nested : ∀ depth, Fin.init (path (depth + 1)) = path depth)
    (coarse fine : ℕ) :
    ∃ suffix : Fin (fine + 1) → (Fin rule.edges × Bool),
      path ((coarse + 1) + (fine + 1)) = Fin.append (path (coarse + 1)) suffix ∧
      path (coarse + fine + 2) = blockWordAppendCompletion20261011 coarse fine (path (coarse + 1)) suffix := by
  obtain ⟨suffix, decomposition⟩ := nested_path_block_decomposition_completion20261011 path nested coarse fine
  refine ⟨suffix, ?_, decomposition⟩
  apply List.ofFn_injective
  rw [List.ofFn_fin_append]
  have lists := congrArg List.ofFn decomposition
  rw [block_word_append_ofFn_completion20261011] at lists
  have reindex := congrArg (fun depth => List.ofFn (path depth))
    (by omega : (coarse + 1) + (fine + 1) = coarse + fine + 2)
  exact reindex.trans lists

/-- The actual cylinder-collar avoidance event gives internal trace roots
of the path's chosen refinement, rather than merely an abstract separation input. -/
theorem actual_noncollar_path_refined_roots_internal_completion20261011
    (rule : Rule) (path : Π depth, Fin depth → (Fin rule.edges × Bool))
    (nested : ∀ depth, Fin.init (path (depth + 1)) = path depth)
    (coarse fine : ℕ)
    (avoids : path ∉ terminalCylinderCollarCompletion20261011 rule 0 (coarse + 1) (fine + 1)) :
    ∃ suffix : Fin (fine + 1) → (Fin rule.edges × Bool),
      path (coarse + fine + 2) = blockWordAppendCompletion20261011 coarse fine (path (coarse + 1)) suffix ∧
      ∀ side : Bool, (fun index => (suffix index).1) ∉
        actualTerminalSocketSetCompletion20261011 rule 0 (fine + 1) side := by
  obtain ⟨suffix, uncast, decomposition⟩ := nested_path_uncast_block_decomposition_completion20261011 rule path nested coarse fine
  refine ⟨suffix, decomposition, ?_⟩
  apply actual_noncollar_path_suffix_completion20261011 rule (coarse + 1) (fine + 1)
    path (path (coarse + 1)) (fun index => (suffix index).1) (fun index => (suffix index).2) ?_ avoids
  simpa only [Prod.eta] using uncast

end
end IGSIII34.Spectral
