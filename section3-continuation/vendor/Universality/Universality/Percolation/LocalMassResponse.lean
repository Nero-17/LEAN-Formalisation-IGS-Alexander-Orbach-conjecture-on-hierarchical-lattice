import Universality.Graph.SubstitutionStates
import Universality.Percolation.ProductDisintegration

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

theorem active_adj_eq (σ : LiveState) (ω : Configuration outerEdges)
    {u v : Fin outerVertices} (hadj : (R.openGraph ω).Adj u v) :
    R.active σ ω u = R.active σ ω v := by
  have reach (root : Fin outerVertices) :
      (R.openGraph ω).reachableDecide root u = (R.openGraph ω).reachableDecide root v := by
    apply Bool.eq_iff_iff.mpr
    simp only [SimpleGraph.reachableDecide_eq_true]
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  unfold active
  rw [reach R.source, reach R.target]

theorem active_endpoints_eq_of_open (σ : LiveState) (ω : Configuration outerEdges)
    (e : Fin outerEdges) (he : ω e = true) :
    R.active σ ω (R.endpoint e).1 = R.active σ ω (R.endpoint e).2 := by
  apply R.active_adj_eq σ ω
  exact ⟨R.loopless e, e, he, Or.inl rfl⟩

theorem conditioningProbability_connected (p : ℝ) :
    S.conditioningProbability p .connected = S.reliability p := rfl

theorem conditioningProbability_both (p : ℝ) :
    S.conditioningProbability p .both = 1 - S.reliability p := by
  have h := S.local_coarse_weight p false
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [← h]
  unfold conditioningProbability conditioning
  apply Finset.sum_congr rfl
  intro ω _
  cases S.crosses ω <;> rfl

theorem conditioningProbability_single (p : ℝ) :
    S.conditioningProbability p .single = 1 - S.reliability p :=
  S.conditioningProbability_both p

theorem conditionalCellResponse_connected (p : ℝ) (τ : LiveState) :
    S.conditionalCellResponse p true (fun cell => S.liveCount .connected τ cell) =
      S.massMatrix p .connected τ := rfl

theorem conditionalCellResponse_both (p : ℝ) (τ : LiveState) :
    S.conditionalCellResponse p false (fun cell => S.liveCount .both τ cell) =
      S.massMatrix p .both τ := by
  unfold massMatrix
  rw [S.conditioningProbability_both]
  unfold conditionalCellResponse
  congr 1
  apply Finset.sum_congr rfl
  intro cell _
  unfold conditioning
  cases S.crosses cell <;> rfl

theorem conditionalCellResponse_single (p : ℝ) (τ : LiveState) :
    S.conditionalCellResponse p false (fun cell => S.liveCount .single τ cell) =
      S.massMatrix p .single τ := by
  unfold massMatrix
  rw [S.conditioningProbability_single]
  unfold conditionalCellResponse
  congr 1
  apply Finset.sum_congr rfl
  intro cell _
  unfold conditioning
  cases S.crosses cell <;> rfl

def localLiveCount (coarse : Configuration outerEdges) (cell : Configuration innerEdges)
    (σ τ : LiveState) (edge : Fin outerEdges) : ℕ :=
  if R.active σ coarse (R.endpoint edge).1 then
    if R.active σ coarse (R.endpoint edge).2 then
      if coarse edge then S.liveCount .connected τ cell else S.liveCount .both τ cell
    else S.liveCount .single τ cell
  else
    if R.active σ coarse (R.endpoint edge).2 then S.reverse.liveCount .single τ cell
    else 0

def substitutedLiveCount (σ τ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) : ℕ := by
  classical
  exact ∑ edge : Fin outerEdges,
    (Finset.univ.filter fun child : Fin innerEdges =>
      R.substitutedChildState S σ ω edge child = some τ).card

theorem substitutedLiveCount_eq_local (σ τ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) :
    R.substitutedLiveCount S σ τ ω =
      ∑ edge : Fin outerEdges, R.localLiveCount S (S.coarseConfiguration ω) (ω edge) σ τ edge := by
  classical
  unfold substitutedLiveCount
  apply Finset.sum_congr rfl
  intro edge _
  simp_rw [R.substitutedChildState_eq_local]
  unfold localLiveCount localChildState
  cases ha : R.active σ (S.coarseConfiguration ω) (R.endpoint edge).1 <;>
    cases hb : R.active σ (S.coarseConfiguration ω) (R.endpoint edge).2 <;>
    cases hc : S.crosses (ω edge) <;>
    simp only [coarseConfiguration, hc, Bool.false_eq_true, ↓reduceIte, liveCount]
  all_goals simp

theorem reliability_reverse (p : ℝ) : S.reverse.reliability p = S.reliability p := by
  simp only [reliability, crosses_reverse]

theorem conditionalCellResponse_reverse (p : ℝ) (opened : Bool)
    (response : Configuration innerEdges → ℝ) :
    S.reverse.conditionalCellResponse p opened response =
      S.conditionalCellResponse p opened response := by
  simp only [conditionalCellResponse, crosses_reverse, reliability_reverse]

theorem localLiveCount_conditional_response (p : ℝ) (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (σ τ : LiveState) (edge : Fin outerEdges) :
    S.conditionalCellResponse p (coarse edge)
      (fun cell => R.localLiveCount S coarse cell σ τ edge) =
      match R.childState σ coarse edge with
      | some state => S.massMatrix p state τ
      | none => 0 := by
  have hreverse : S.conditionalCellResponse p false
      (fun cell => S.reverse.liveCount .single τ cell) = S.massMatrix p .single τ := by
    rw [← S.conditionalCellResponse_reverse]
    rw [S.reverse.conditionalCellResponse_single, symmetry.massMatrix_reverse hs ht]
  have hclosed : coarse edge = true →
      R.active σ coarse (R.endpoint edge).1 = R.active σ coarse (R.endpoint edge).2 :=
    R.active_endpoints_eq_of_open σ coarse edge
  unfold localLiveCount childState
  cases ha : R.active σ coarse (R.endpoint edge).1 <;>
    cases hb : R.active σ coarse (R.endpoint edge).2 <;>
    cases hc : coarse edge <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and,
      Bool.false_or, Bool.or_false, Nat.cast_zero]
  · simp [conditionalCellResponse]
  · simp [conditionalCellResponse]
  · exact hreverse
  · have h := hclosed hc
    rw [ha, hb] at h
    contradiction
  · exact S.conditionalCellResponse_single p τ
  · have h := hclosed hc
    rw [ha, hb] at h
    contradiction
  · exact S.conditionalCellResponse_both p τ
  · exact S.conditionalCellResponse_connected p τ

end
end Universality.FiniteNetwork
