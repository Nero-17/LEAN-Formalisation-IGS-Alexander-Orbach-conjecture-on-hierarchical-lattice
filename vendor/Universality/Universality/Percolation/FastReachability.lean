import Universality.Percolation.FiniteNetwork

/-!
# Edge-indexed breadth-first search

Scanning the open edges once per layer avoids repeatedly deciding adjacency
for every pair of vertices.  The result is proved equal to the graph-theoretic
ball before it is used to accelerate finite certificates.
-/

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def expandEdges (ω : Configuration edges) (S : Finset (Fin vertices)) :
    Finset (Fin vertices) :=
  S ∪ Finset.univ.biUnion (fun e : Fin edges =>
    if ω e = true ∧ ((R.endpoint e).1 ∈ S ∨ (R.endpoint e).2 ∈ S)
    then {(R.endpoint e).1, (R.endpoint e).2} else ∅)

theorem expandEdges_eq (ω : Configuration edges) (S : Finset (Fin vertices)) :
    R.expandEdges ω S = S ∪ S.biUnion (fun v => (R.openGraph ω).neighborFinset v) := by
  ext v
  have mem_if (e : Fin edges) :
      v ∈ (if ω e = true ∧ ((R.endpoint e).1 ∈ S ∨ (R.endpoint e).2 ∈ S)
        then {(R.endpoint e).1, (R.endpoint e).2} else (∅ : Finset (Fin vertices))) ↔
      (ω e = true ∧ ((R.endpoint e).1 ∈ S ∨ (R.endpoint e).2 ∈ S)) ∧
        (v = (R.endpoint e).1 ∨ v = (R.endpoint e).2) := by
    split <;> simp_all
  simp only [expandEdges, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
    true_and, mem_if, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (hv | ⟨e, ⟨he, hs | ht⟩, hv | hv⟩)
    · exact Or.inl hv
    · exact Or.inl (hv.symm ▸ hs)
    · right
      refine ⟨(R.endpoint e).1, hs, ?_⟩
      exact ⟨hv ▸ R.loopless e, e, he, Or.inl (Prod.ext rfl hv.symm)⟩
    · right
      refine ⟨(R.endpoint e).2, ht, ?_⟩
      exact ⟨hv ▸ (R.loopless e).symm, e, he, Or.inr (Prod.ext hv.symm rfl)⟩
    · exact Or.inl (hv.symm ▸ ht)
  · rintro (hv | ⟨u, hu, hne, e, he, hpair | hpair⟩)
    · exact Or.inl hv
    · right
      refine ⟨e, ⟨he, Or.inl ?_⟩, Or.inr ?_⟩ <;> simp [hpair, hu]
    · right
      refine ⟨e, ⟨he, Or.inr ?_⟩, Or.inl ?_⟩ <;> simp [hpair, hu]

def edgeBall (ω : Configuration edges) (root : Fin vertices) : ℕ → Finset (Fin vertices)
  | 0 => {root}
  | n + 1 => R.expandEdges ω (edgeBall ω root n)

theorem edgeBall_eq (ω : Configuration edges) (root : Fin vertices) (n : ℕ) :
    R.edgeBall ω root n = (R.openGraph ω).reachableBall root n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [edgeBall, expandEdges_eq, ih]; rfl

def fastReachable (ω : Configuration edges) (root v : Fin vertices) : Bool :=
  decide (v ∈ R.edgeBall ω root vertices)

theorem fastReachable_eq (ω : Configuration edges) (root v : Fin vertices) :
    R.fastReachable ω root v = (R.openGraph ω).reachableDecide root v := by
  simp only [fastReachable, SimpleGraph.reachableDecide, edgeBall_eq, Fintype.card_fin]

def fastConditioningCount (σ : LiveState) : ℕ :=
  (Finset.univ.filter fun ω : Configuration edges =>
    (match σ with
      | .connected => R.fastReachable ω R.source R.target
      | .both | .single => !(R.fastReachable ω R.source R.target)) = true).card

theorem fastConditioningCount_eq (σ : LiveState) :
    R.fastConditioningCount σ = R.conditioningCount σ := by
  cases σ <;> simp only [fastConditioningCount, conditioningCount, conditioning,
    fastReachable_eq, crosses]

def fastConditionalCount (σ τ : LiveState) : ℕ :=
  ∑ ω : Configuration edges,
    let fromSource := R.edgeBall ω R.source vertices
    let fromTarget := R.edgeBall ω R.target vertices
    let crossing := decide (R.target ∈ fromSource)
    let condition := match σ with
      | .connected => crossing
      | .both | .single => !crossing
    let activeVertex := fun v => decide (v ∈ fromSource) ||
      (σ == .both && decide (v ∈ fromTarget))
    if condition then
      (Finset.univ.filter fun e : Fin edges =>
        (let first := activeVertex (R.endpoint e).1
         let second := activeVertex (R.endpoint e).2
         if first && second then
           if ω e then some LiveState.connected else some LiveState.both
         else if first || second then some LiveState.single else none) = some τ).card
    else 0

theorem fastConditionalCount_eq (σ τ : LiveState) :
    R.fastConditionalCount σ τ = R.conditionalCount σ τ := by
  unfold fastConditionalCount conditionalCount liveCount childState active
  simp only [edgeBall_eq, SimpleGraph.reachableDecide, Fintype.card_fin,
    conditioning, crosses]
  cases σ <;> rfl

end Universality.FiniteNetwork
