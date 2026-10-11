import Universality.Percolation.FiniteNetwork
import Mathlib.Tactic.SplitIfs

/-!
# Connectivity under edge substitution

Each outer edge gets its own copy of the inner vertices.  Only its two
terminals are glued to the endpoints of that outer edge.  Connectivity is
proved equivalent to connectivity in the coarse graph of connected cells.
-/

namespace Universality.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

def InteriorVertex := {v : Fin innerVertices // v ≠ S.source ∧ v ≠ S.target}

def SubstitutionVertex (_R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) :=
  Fin outerVertices ⊕ (Fin outerEdges × S.InteriorVertex)

def cellVertex (e : Fin outerEdges) (x : Fin innerVertices) : R.SubstitutionVertex S :=
  if hs : x = S.source then Sum.inl (R.endpoint e).1
  else if ht : x = S.target then Sum.inl (R.endpoint e).2
  else Sum.inr (e, ⟨x, hs, ht⟩)

theorem cellVertex_source (e : Fin outerEdges) :
    R.cellVertex S e S.source = Sum.inl (R.endpoint e).1 := by simp [cellVertex]

theorem cellVertex_target (e : Fin outerEdges) :
    R.cellVertex S e S.target = Sum.inl (R.endpoint e).2 := by
  simp [cellVertex, Ne.symm S.terminals_distinct]

theorem cellVertex_injective (e : Fin outerEdges) : Function.Injective (R.cellVertex S e) := by
  intro x y h
  unfold cellVertex at h
  split_ifs at h <;> simp_all [S.terminals_distinct]
  · exact R.loopless e (Sum.inl.inj h)
  · exact R.loopless e (Sum.inl.inj h).symm
  · exact congrArg (fun p : Fin outerEdges × S.InteriorVertex => p.2.val) (Sum.inr.inj h)

def substitutedGraph (ω : Fin outerEdges → Configuration innerEdges) :
    SimpleGraph (R.SubstitutionVertex S) where
  Adj u v := u ≠ v ∧ ∃ e x y, (S.openGraph (ω e)).Adj x y ∧
    R.cellVertex S e x = u ∧ R.cellVertex S e y = v
  symm := ⟨by
    rintro u v ⟨hne, e, x, y, hxy, rfl, rfl⟩
    exact ⟨hne.symm, e, y, x, hxy.symm, rfl, rfl⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def coarseConfiguration (ω : Fin outerEdges → Configuration innerEdges) :
    Configuration outerEdges := fun e => S.crosses (ω e)

def cellHom (ω : Fin outerEdges → Configuration innerEdges) (e : Fin outerEdges) :
    S.openGraph (ω e) →g R.substitutedGraph S ω where
  toFun := R.cellVertex S e
  map_rel' := by
    intro x y h
    exact ⟨fun heq => h.ne (R.cellVertex_injective S e heq), e, x, y, h, rfl, rfl⟩

theorem coarseAdj_reachable (ω : Fin outerEdges → Configuration innerEdges)
    {u v : Fin outerVertices}
    (h : (R.openGraph (S.coarseConfiguration ω)).Adj u v) :
    (R.substitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) := by
  obtain ⟨_, e, he, hpair | hpair⟩ := h
  · have hc := (S.crosses_eq_true (ω e)).mp he
    have hm := hc.map (R.cellHom S ω e)
    change (R.substitutedGraph S ω).Reachable
      (R.cellVertex S e S.source) (R.cellVertex S e S.target) at hm
    rw [cellVertex_source, cellVertex_target] at hm
    simpa only [hpair] using hm
  · have hc := (S.crosses_eq_true (ω e)).mp he
    have hm := hc.map (R.cellHom S ω e)
    change (R.substitutedGraph S ω).Reachable
      (R.cellVertex S e S.source) (R.cellVertex S e S.target) at hm
    rw [cellVertex_source, cellVertex_target] at hm
    simpa only [hpair] using hm.symm

theorem coarseReachable_lifts (ω : Fin outerEdges → Configuration innerEdges)
    {u v : Fin outerVertices}
    (h : (R.openGraph (S.coarseConfiguration ω)).Reachable u v) :
    (R.substitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact .refl _
  | cons hadj walk ih => exact (R.coarseAdj_reachable S ω hadj).trans ih

theorem coarseCellReachable (ω : Fin outerEdges → Configuration innerEdges)
    (e : Fin outerEdges) (h : (S.openGraph (ω e)).Reachable S.source S.target) :
    (R.openGraph (S.coarseConfiguration ω)).Reachable
      (R.endpoint e).1 (R.endpoint e).2 := by
  apply SimpleGraph.Adj.reachable
  exact ⟨R.loopless e, e, (S.crosses_eq_true (ω e)).mpr h, Or.inl rfl⟩

def substitutionActive (ω : Fin outerEdges → Configuration innerEdges)
    (root : Fin outerVertices) : R.SubstitutionVertex S → Prop
  | .inl v => (R.openGraph (S.coarseConfiguration ω)).Reachable root v
  | .inr (e, x) =>
      ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).1 ∧
        (S.openGraph (ω e)).Reachable S.source x.val) ∨
      ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).2 ∧
        (S.openGraph (ω e)).Reachable S.target x.val)

theorem substitutionActive_cell (ω : Fin outerEdges → Configuration innerEdges)
    (root : Fin outerVertices) (e : Fin outerEdges) (x : Fin innerVertices) :
    R.substitutionActive S ω root (R.cellVertex S e x) ↔
      ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).1 ∧
        (S.openGraph (ω e)).Reachable S.source x) ∨
      ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).2 ∧
        (S.openGraph (ω e)).Reachable S.target x) := by
  by_cases hs : x = S.source
  · subst x
    rw [cellVertex_source]
    change (R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).1 ↔ _
    constructor
    · intro h
      exact Or.inl ⟨h, .refl _⟩
    · rintro (⟨h, _⟩ | ⟨h, hcell⟩)
      · exact h
      · exact h.trans (R.coarseCellReachable S ω e hcell.symm).symm
  · by_cases ht : x = S.target
    · subst x
      rw [cellVertex_target]
      change (R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).2 ↔ _
      constructor
      · intro h
        exact Or.inr ⟨h, .refl _⟩
      · rintro (⟨h, hcell⟩ | ⟨h, _⟩)
        · exact h.trans (R.coarseCellReachable S ω e hcell)
        · exact h
    · simp only [cellVertex, dif_neg hs, dif_neg ht, substitutionActive]

theorem substitutionActive_adj (ω : Fin outerEdges → Configuration innerEdges)
    (root : Fin outerVertices) {u v : R.SubstitutionVertex S}
    (h : (R.substitutedGraph S ω).Adj u v) (hu : R.substitutionActive S ω root u) :
    R.substitutionActive S ω root v := by
  obtain ⟨_, e, x, y, hxy, rfl, rfl⟩ := h
  rw [substitutionActive_cell] at hu ⊢
  rcases hu with ⟨houter, hinner⟩ | ⟨houter, hinner⟩
  · exact Or.inl ⟨houter, hinner.trans hxy.reachable⟩
  · exact Or.inr ⟨houter, hinner.trans hxy.reachable⟩

theorem substitutedReachable_descends (ω : Fin outerEdges → Configuration innerEdges)
    {u v : Fin outerVertices}
    (h : (R.substitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v)) :
    (R.openGraph (S.coarseConfiguration ω)).Reachable u v := by
  have propagate {a b : R.SubstitutionVertex S} (walk : (R.substitutedGraph S ω).Walk a b) :
      R.substitutionActive S ω u a → R.substitutionActive S ω u b := by
    induction walk with
    | nil => exact id
    | cons hadj walk ih =>
        intro ha
        exact ih (R.substitutionActive_adj S ω u hadj ha)
  obtain ⟨walk⟩ := h
  exact propagate walk (SimpleGraph.Reachable.refl u)

theorem substitutedReachable_iff (ω : Fin outerEdges → Configuration innerEdges)
    (u v : Fin outerVertices) :
    (R.substitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) ↔
      (R.openGraph (S.coarseConfiguration ω)).Reachable u v :=
  ⟨R.substitutedReachable_descends S ω, R.coarseReachable_lifts S ω⟩

theorem substitutedReachable_iff_active (ω : Fin outerEdges → Configuration innerEdges)
    (root : Fin outerVertices) (v : R.SubstitutionVertex S) :
    (R.substitutedGraph S ω).Reachable (Sum.inl root) v ↔
      R.substitutionActive S ω root v := by
  constructor
  · intro h
    have propagate {a b : R.SubstitutionVertex S} (walk : (R.substitutedGraph S ω).Walk a b) :
        R.substitutionActive S ω root a → R.substitutionActive S ω root b := by
      induction walk with
      | nil => exact id
      | cons hadj walk ih =>
          exact fun ha => ih (R.substitutionActive_adj S ω root hadj ha)
    obtain ⟨walk⟩ := h
    exact propagate walk (SimpleGraph.Reachable.refl root)
  · cases v with
    | inl v => exact R.coarseReachable_lifts S ω
    | inr cell =>
        obtain ⟨e, x⟩ := cell
        intro h
        change
          ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).1 ∧
            (S.openGraph (ω e)).Reachable S.source x.val) ∨
          ((R.openGraph (S.coarseConfiguration ω)).Reachable root (R.endpoint e).2 ∧
            (S.openGraph (ω e)).Reachable S.target x.val) at h
        have hx : R.cellVertex S e x.val = Sum.inr (e, x) := by
          simp only [cellVertex, dif_neg x.property.1, dif_neg x.property.2]
          rfl
        rcases h with ⟨houter, hinner⟩ | ⟨houter, hinner⟩
        · have hm := hinner.map (R.cellHom S ω e)
          change (R.substitutedGraph S ω).Reachable
            (R.cellVertex S e S.source) (R.cellVertex S e x.val) at hm
          rw [cellVertex_source, hx] at hm
          exact (R.coarseReachable_lifts S ω houter).trans hm
        · have hm := hinner.map (R.cellHom S ω e)
          change (R.substitutedGraph S ω).Reachable
            (R.cellVertex S e S.target) (R.cellVertex S e x.val) at hm
          rw [cellVertex_target, hx] at hm
          exact (R.coarseReachable_lifts S ω houter).trans hm

end Universality.FiniteNetwork
