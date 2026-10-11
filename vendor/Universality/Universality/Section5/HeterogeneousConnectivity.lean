import Universality.Graph.Substitution

/-! Connectivity for edge-dependent finite replacement networks.
This extends the uniform substitution construction without assuming equal
numbers of vertices or edges in the different cells. -/

namespace Universality.FiniteNetwork

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

def HeterogeneousVertex (_R : FiniteNetwork outerVertices outerEdges)
    (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge)) :=
  Fin outerVertices ⊕ (Σ edge : Fin outerEdges, (S edge).InteriorVertex)

def heterogeneousCellVertex (e : Fin outerEdges) (x : Fin (innerVertices e)) : R.HeterogeneousVertex S :=
  if hs : x = (S e).source then Sum.inl (R.endpoint e).1
  else if ht : x = (S e).target then Sum.inl (R.endpoint e).2
  else Sum.inr ⟨e, ⟨x, hs, ht⟩⟩

theorem heterogeneousCellVertex_source (e : Fin outerEdges) :
    R.heterogeneousCellVertex S e (S e).source = Sum.inl (R.endpoint e).1 := by simp [heterogeneousCellVertex]

theorem heterogeneousCellVertex_target (e : Fin outerEdges) :
    R.heterogeneousCellVertex S e (S e).target = Sum.inl (R.endpoint e).2 := by
  simp [heterogeneousCellVertex, Ne.symm (S e).terminals_distinct]

theorem heterogeneousCellVertex_injective (e : Fin outerEdges) : Function.Injective (R.heterogeneousCellVertex S e) := by
  intro x y h
  unfold heterogeneousCellVertex at h
  split_ifs at h <;> simp_all [(S e).terminals_distinct]
  · exact R.loopless e (Sum.inl.inj h)
  · exact R.loopless e (Sum.inl.inj h).symm
  · exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2)

def heterogeneousSubstitutedGraph (ω : (e : Fin outerEdges) → Configuration (innerEdges e)) :
    SimpleGraph (R.HeterogeneousVertex S) where
  Adj u v := u ≠ v ∧ ∃ e x y, ((S e).openGraph (ω e)).Adj x y ∧
    R.heterogeneousCellVertex S e x = u ∧ R.heterogeneousCellVertex S e y = v
  symm := ⟨by
    rintro u v ⟨hne, e, x, y, hxy, rfl, rfl⟩
    exact ⟨hne.symm, e, y, x, hxy.symm, rfl, rfl⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def heterogeneousCoarseConfiguration (ω : (e : Fin outerEdges) → Configuration (innerEdges e)) :
    Configuration outerEdges := fun e => (S e).crosses (ω e)

def heterogeneousCellHom (ω : (e : Fin outerEdges) → Configuration (innerEdges e)) (e : Fin outerEdges) :
    (S e).openGraph (ω e) →g R.heterogeneousSubstitutedGraph S ω where
  toFun := R.heterogeneousCellVertex S e
  map_rel' := by
    intro x y h
    exact ⟨fun heq => h.ne (R.heterogeneousCellVertex_injective S e heq), e, x, y, h, rfl, rfl⟩

theorem heterogeneousCoarseAdj_reachable (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    {u v : Fin outerVertices}
    (h : (R.openGraph (heterogeneousCoarseConfiguration S ω)).Adj u v) :
    (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) := by
  obtain ⟨_, e, he, hpair | hpair⟩ := h
  · have hc := ((S e).crosses_eq_true (ω e)).mp he
    have hm := hc.map (R.heterogeneousCellHom S ω e)
    change (R.heterogeneousSubstitutedGraph S ω).Reachable
      (R.heterogeneousCellVertex S e (S e).source) (R.heterogeneousCellVertex S e (S e).target) at hm
    rw [heterogeneousCellVertex_source, heterogeneousCellVertex_target] at hm
    simpa only [hpair] using hm
  · have hc := ((S e).crosses_eq_true (ω e)).mp he
    have hm := hc.map (R.heterogeneousCellHom S ω e)
    change (R.heterogeneousSubstitutedGraph S ω).Reachable
      (R.heterogeneousCellVertex S e (S e).source) (R.heterogeneousCellVertex S e (S e).target) at hm
    rw [heterogeneousCellVertex_source, heterogeneousCellVertex_target] at hm
    simpa only [hpair] using hm.symm

theorem heterogeneousCoarseReachable_lifts (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    {u v : Fin outerVertices}
    (h : (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable u v) :
    (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact .refl _
  | cons hadj walk ih => exact (R.heterogeneousCoarseAdj_reachable S ω hadj).trans ih

theorem heterogeneousCoarseCellReachable (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (e : Fin outerEdges) (h : ((S e).openGraph (ω e)).Reachable (S e).source (S e).target) :
    (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable
      (R.endpoint e).1 (R.endpoint e).2 := by
  apply SimpleGraph.Adj.reachable
  exact ⟨R.loopless e, e, ((S e).crosses_eq_true (ω e)).mpr h, Or.inl rfl⟩

def heterogeneousSubstitutionActive (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (root : Fin outerVertices) : R.HeterogeneousVertex S → Prop
  | .inl v => (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root v
  | .inr ⟨e, x⟩ =>
      ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).1 ∧
        ((S e).openGraph (ω e)).Reachable (S e).source x.val) ∨
      ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).2 ∧
        ((S e).openGraph (ω e)).Reachable (S e).target x.val)

theorem heterogeneousSubstitutionActive_cell (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (root : Fin outerVertices) (e : Fin outerEdges) (x : Fin (innerVertices e)) :
    R.heterogeneousSubstitutionActive S ω root (R.heterogeneousCellVertex S e x) ↔
      ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).1 ∧
        ((S e).openGraph (ω e)).Reachable (S e).source x) ∨
      ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).2 ∧
        ((S e).openGraph (ω e)).Reachable (S e).target x) := by
  by_cases hs : x = (S e).source
  · subst x
    rw [heterogeneousCellVertex_source]
    change (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).1 ↔ _
    constructor
    · intro h
      exact Or.inl ⟨h, .refl _⟩
    · rintro (⟨h, _⟩ | ⟨h, hcell⟩)
      · exact h
      · exact h.trans (R.heterogeneousCoarseCellReachable S ω e hcell.symm).symm
  · by_cases ht : x = (S e).target
    · subst x
      rw [heterogeneousCellVertex_target]
      change (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).2 ↔ _
      constructor
      · intro h
        exact Or.inr ⟨h, .refl _⟩
      · rintro (⟨h, hcell⟩ | ⟨h, _⟩)
        · exact h.trans (R.heterogeneousCoarseCellReachable S ω e hcell)
        · exact h
    · simp only [heterogeneousCellVertex, dif_neg hs, dif_neg ht, heterogeneousSubstitutionActive]

theorem heterogeneousSubstitutionActive_adj (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (root : Fin outerVertices) {u v : R.HeterogeneousVertex S}
    (h : (R.heterogeneousSubstitutedGraph S ω).Adj u v) (hu : R.heterogeneousSubstitutionActive S ω root u) :
    R.heterogeneousSubstitutionActive S ω root v := by
  obtain ⟨_, e, x, y, hxy, rfl, rfl⟩ := h
  rw [heterogeneousSubstitutionActive_cell] at hu ⊢
  rcases hu with ⟨houter, hinner⟩ | ⟨houter, hinner⟩
  · exact Or.inl ⟨houter, hinner.trans hxy.reachable⟩
  · exact Or.inr ⟨houter, hinner.trans hxy.reachable⟩

theorem heterogeneousSubstitutedReachable_descends (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    {u v : Fin outerVertices}
    (h : (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v)) :
    (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable u v := by
  have propagate {a b : R.HeterogeneousVertex S} (walk : (R.heterogeneousSubstitutedGraph S ω).Walk a b) :
      R.heterogeneousSubstitutionActive S ω u a → R.heterogeneousSubstitutionActive S ω u b := by
    induction walk with
    | nil => exact id
    | cons hadj walk ih =>
        intro ha
        exact ih (R.heterogeneousSubstitutionActive_adj S ω u hadj ha)
  obtain ⟨walk⟩ := h
  exact propagate walk (SimpleGraph.Reachable.refl u)

theorem heterogeneousSubstitutedReachable_iff (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (u v : Fin outerVertices) :
    (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl u) (Sum.inl v) ↔
      (R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable u v :=
  ⟨R.heterogeneousSubstitutedReachable_descends S ω, R.heterogeneousCoarseReachable_lifts S ω⟩

theorem heterogeneousSubstitutedReachable_iff_active (ω : (e : Fin outerEdges) → Configuration (innerEdges e))
    (root : Fin outerVertices) (v : R.HeterogeneousVertex S) :
    (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl root) v ↔
      R.heterogeneousSubstitutionActive S ω root v := by
  constructor
  · intro h
    have propagate {a b : R.HeterogeneousVertex S} (walk : (R.heterogeneousSubstitutedGraph S ω).Walk a b) :
        R.heterogeneousSubstitutionActive S ω root a → R.heterogeneousSubstitutionActive S ω root b := by
      induction walk with
      | nil => exact id
      | cons hadj walk ih =>
          exact fun ha => ih (R.heterogeneousSubstitutionActive_adj S ω root hadj ha)
    obtain ⟨walk⟩ := h
    exact propagate walk (SimpleGraph.Reachable.refl root)
  · cases v with
    | inl v => exact R.heterogeneousCoarseReachable_lifts S ω
    | inr cell =>
        obtain ⟨e, x⟩ := cell
        intro h
        change
          ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).1 ∧
            ((S e).openGraph (ω e)).Reachable (S e).source x.val) ∨
          ((R.openGraph (heterogeneousCoarseConfiguration S ω)).Reachable root (R.endpoint e).2 ∧
            ((S e).openGraph (ω e)).Reachable (S e).target x.val) at h
        have hx : R.heterogeneousCellVertex S e x.val = Sum.inr ⟨e, x⟩ := by
          simp only [heterogeneousCellVertex, dif_neg x.property.1, dif_neg x.property.2]
          rfl
        rcases h with ⟨houter, hinner⟩ | ⟨houter, hinner⟩
        · have hm := hinner.map (R.heterogeneousCellHom S ω e)
          change (R.heterogeneousSubstitutedGraph S ω).Reachable
            (R.heterogeneousCellVertex S e (S e).source) (R.heterogeneousCellVertex S e x.val) at hm
          rw [heterogeneousCellVertex_source, hx] at hm
          exact (R.heterogeneousCoarseReachable_lifts S ω houter).trans hm
        · have hm := hinner.map (R.heterogeneousCellHom S ω e)
          change (R.heterogeneousSubstitutedGraph S ω).Reachable
            (R.heterogeneousCellVertex S e (S e).target) (R.heterogeneousCellVertex S e x.val) at hm
          rw [heterogeneousCellVertex_target, hx] at hm
          exact (R.heterogeneousCoarseReachable_lifts S ω houter).trans hm

end Universality.FiniteNetwork
