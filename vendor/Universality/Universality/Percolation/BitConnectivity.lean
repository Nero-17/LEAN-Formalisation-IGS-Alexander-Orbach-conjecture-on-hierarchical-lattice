import Universality.Percolation.FastReachability
import Mathlib.Tactic.Tauto

/-!
# Bit-vector connectivity certificates

The executable state stores one bit per vertex.  Its semantic relation to
the graph-theoretic vertex set is proved layer by layer.
-/

namespace Universality.FiniteNetwork

def vertexMask {vertices : ℕ} (v : Fin vertices) : BitVec vertices :=
  (1 : BitVec vertices) <<< v.val

theorem vertexMask_test {vertices : ℕ} (u v : Fin vertices) :
    (vertexMask u).getLsbD v.val = true ↔ v = u := by
  rw [vertexMask, BitVec.getLsbD_shiftLeft]
  change (decide (v.val < vertices) && !decide (v.val < u.val) &&
    (1#vertices).getLsbD (v.val - u.val)) = true ↔ v = u
  rw [BitVec.getLsbD_one]
  simp only [
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  have hu := u.isLt
  have hv := v.isLt
  simp only [Fin.ext_iff]
  omega

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def maskNeighbors (ω : Configuration edges) (current : BitVec vertices) :
    List (Fin edges) → BitVec vertices
  | [] => 0
  | e :: rest =>
      let remaining := maskNeighbors ω current rest
      if ω e && (current.getLsbD (R.endpoint e).1.val ||
          current.getLsbD (R.endpoint e).2.val)
      then vertexMask (R.endpoint e).1 ||| vertexMask (R.endpoint e).2 ||| remaining
      else remaining

set_option maxHeartbeats 1000000 in
theorem maskNeighbors_test (ω : Configuration edges) (current : BitVec vertices)
    (L : List (Fin edges)) (v : Fin vertices) :
    (R.maskNeighbors ω current L).getLsbD v.val = true ↔
      ∃ e ∈ L, ω e = true ∧
        (current.getLsbD (R.endpoint e).1.val = true ∨
          current.getLsbD (R.endpoint e).2.val = true) ∧
        (v = (R.endpoint e).1 ∨ v = (R.endpoint e).2) := by
  induction L with
  | nil => simp [maskNeighbors]
  | cons e rest ih =>
      simp only [maskNeighbors]
      split <;> rename_i h
      · simp only [BitVec.getLsbD_or, Bool.or_eq_true, vertexMask_test, ih,
          List.mem_cons, exists_eq_or_imp]
        simp_all only [Bool.and_eq_true, Bool.or_eq_true]
        simp only [true_and]
      · simp only [ih, List.mem_cons, exists_eq_or_imp]
        simp_all only [Bool.and_eq_true, Bool.or_eq_true]
        constructor
        · exact Or.inr
        · rintro (⟨he, hactive, _⟩ | hrest)
          · exact False.elim (h ⟨he, hactive⟩)
          · exact hrest

def maskExpand (ω : Configuration edges) (current : BitVec vertices) : BitVec vertices :=
  current ||| R.maskNeighbors ω current (List.finRange edges)

theorem maskExpand_test (ω : Configuration edges) (current : BitVec vertices)
    (S : Finset (Fin vertices))
    (hS : ∀ v : Fin vertices, current.getLsbD v.val = true ↔ v ∈ S)
    (v : Fin vertices) :
    (R.maskExpand ω current).getLsbD v.val = true ↔ v ∈ R.expandEdges ω S := by
  simp only [maskExpand, BitVec.getLsbD_or, Bool.or_eq_true, maskNeighbors_test,
    List.mem_finRange, Finset.mem_univ, true_and, hS, expandEdges, Finset.mem_union,
    Finset.mem_biUnion]
  apply or_congr Iff.rfl
  apply exists_congr
  intro e
  split_ifs <;> simp_all

def bitBall (ω : Configuration edges) (root : Fin vertices) : ℕ → BitVec vertices
  | 0 => vertexMask root
  | n + 1 => R.maskExpand ω (bitBall ω root n)

theorem bitBall_test (ω : Configuration edges) (root v : Fin vertices) (n : ℕ) :
    (R.bitBall ω root n).getLsbD v.val = true ↔ v ∈ R.edgeBall ω root n := by
  induction n generalizing v with
  | zero => simp only [bitBall, vertexMask_test, edgeBall, Finset.mem_singleton]
  | succ n ih =>
      rw [bitBall, edgeBall]
      apply maskExpand_test
      intro u
      exact ih u

def bitReachable (ω : Configuration edges) (root v : Fin vertices) : Bool :=
  (R.bitBall ω root vertices).getLsbD v.val

theorem bitReachable_eq (ω : Configuration edges) (root v : Fin vertices) :
    R.bitReachable ω root v = (R.openGraph ω).reachableDecide root v := by
  apply Bool.eq_iff_iff.mpr
  simp only [bitReachable, bitBall_test, SimpleGraph.reachableDecide,
    decide_eq_true_eq, Fintype.card_fin, edgeBall_eq]

def bitConditioningCount (σ : LiveState) : ℕ :=
  (Finset.univ.filter fun ω : Configuration edges =>
    (match σ with
      | .connected => R.bitReachable ω R.source R.target
      | .both | .single => !(R.bitReachable ω R.source R.target)) = true).card

theorem bitConditioningCount_eq (σ : LiveState) :
    R.bitConditioningCount σ = R.conditioningCount σ := by
  cases σ <;> simp only [bitConditioningCount, conditioningCount, conditioning,
    bitReachable_eq, crosses]

def bitConditionalCount (σ τ : LiveState) : ℕ :=
  ∑ ω : Configuration edges,
    let fromSource := R.bitBall ω R.source vertices
    let fromTarget := R.bitBall ω R.target vertices
    let crossing := fromSource.getLsbD R.target.val
    let condition := match σ with
      | .connected => crossing
      | .both | .single => !crossing
    let activeVertex := fun v : Fin vertices => fromSource.getLsbD v.val ||
      (σ == .both && fromTarget.getLsbD v.val)
    if condition then
      (Finset.univ.filter fun e : Fin edges =>
        (let first := activeVertex (R.endpoint e).1
         let second := activeVertex (R.endpoint e).2
         if first && second then
           if ω e then some LiveState.connected else some LiveState.both
         else if first || second then some LiveState.single else none) = some τ).card
    else 0

theorem bitConditionalCount_eq (σ τ : LiveState) :
    R.bitConditionalCount σ τ = R.conditionalCount σ τ := by
  unfold bitConditionalCount conditionalCount liveCount childState active
  change (∑ ω : Configuration edges,
    if (match σ with
      | .connected => R.bitReachable ω R.source R.target
      | .both | .single => !(R.bitReachable ω R.source R.target)) then
      (Finset.univ.filter fun e : Fin edges =>
        (let first := R.bitReachable ω R.source (R.endpoint e).1 ||
          (σ == .both && R.bitReachable ω R.target (R.endpoint e).1)
         let second := R.bitReachable ω R.source (R.endpoint e).2 ||
          (σ == .both && R.bitReachable ω R.target (R.endpoint e).2)
         if first && second then
           if ω e then some LiveState.connected else some LiveState.both
         else if first || second then some LiveState.single else none) = some τ).card
    else 0) = _
  simp only [bitReachable_eq, conditioning, crosses]
  cases σ <;> rfl

end Universality.FiniteNetwork
