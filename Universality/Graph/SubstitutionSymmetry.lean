import Universality.Graph.SubstitutionNetwork

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

namespace NetworkSymmetry

def identity : R.NetworkSymmetry where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  endpoint _ := Or.inl rfl

variable {R S}

def interiorEquiv (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source) :
    S.InteriorVertex ≃ S.InteriorVertex :=
  symmetry.vertex.subtypeEquiv (by
    intro v
    change (v ≠ S.source ∧ v ≠ S.target) ↔
      (symmetry.vertex v ≠ S.source ∧ symmetry.vertex v ≠ S.target)
    constructor
    · rintro ⟨hsource, htarget⟩
      constructor
      · intro h; apply htarget; apply symmetry.vertex.injective; exact h.trans ht.symm
      · intro h; apply hsource; apply symmetry.vertex.injective; exact h.trans hs.symm
    · rintro ⟨hsource, htarget⟩
      constructor
      · rintro rfl; exact htarget hs
      · rintro rfl; exact hsource ht)

def respectsOrientation (outerSymmetry : R.NetworkSymmetry) (edge : Fin outerEdges) : Prop :=
  R.endpoint (outerSymmetry.edge edge) =
    (outerSymmetry.vertex (R.endpoint edge).1, outerSymmetry.vertex (R.endpoint edge).2)

instance (outerSymmetry : R.NetworkSymmetry) (edge : Fin outerEdges) :
    Decidable (outerSymmetry.respectsOrientation edge) := inferInstanceAs (Decidable (_ = _))

def orientedInner (outerSymmetry : R.NetworkSymmetry) (innerSymmetry : S.NetworkSymmetry)
    (edge : Fin outerEdges) : S.NetworkSymmetry :=
  if outerSymmetry.respectsOrientation edge then identity S else innerSymmetry

def orientedInterior (outerSymmetry : R.NetworkSymmetry) (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source) (edge : Fin outerEdges) :
    S.InteriorVertex ≃ S.InteriorVertex :=
  if outerSymmetry.respectsOrientation edge then Equiv.refl _
    else innerSymmetry.interiorEquiv hs ht

theorem orientedInterior_val (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source) (edge : Fin outerEdges)
    (v : S.InteriorVertex) :
    (outerSymmetry.orientedInterior innerSymmetry hs ht edge v).val =
      (outerSymmetry.orientedInner innerSymmetry edge).vertex v.val := by
  unfold orientedInterior orientedInner
  split <;> rfl

/-- A product equivalence whose fibre equivalence may depend on the first coordinate. -/
def fibreProduct {α β : Type*} (base : α ≃ α) (fibre : α → β ≃ β) : α × β ≃ α × β where
  toFun pair := (base pair.1, fibre pair.1 pair.2)
  invFun pair := (base.symm pair.1, (fibre (base.symm pair.1)).symm pair.2)
  left_inv pair := by simp
  right_inv pair := by simp

def substitutionVertexEquiv (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source) :
    R.SubstitutionVertex S ≃ R.SubstitutionVertex S :=
  Equiv.sumCongr outerSymmetry.vertex
    (fibreProduct outerSymmetry.edge (outerSymmetry.orientedInterior innerSymmetry hs ht))

def substitutionEdgeEquiv (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry) :
    Fin outerEdges × Fin innerEdges ≃ Fin outerEdges × Fin innerEdges :=
  fibreProduct outerSymmetry.edge (fun edge =>
    (outerSymmetry.orientedInner innerSymmetry edge).edge)

theorem substitutionEdgeEquiv_apply (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry) (edge : Fin outerEdges) (child : Fin innerEdges) :
    outerSymmetry.substitutionEdgeEquiv innerSymmetry (edge, child) =
      (outerSymmetry.edge edge, (outerSymmetry.orientedInner innerSymmetry edge).edge child) := rfl

theorem substitutionVertexEquiv_cell (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source) (edge : Fin outerEdges)
    (v : Fin innerVertices) :
    outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht (R.cellVertex S edge v) =
      R.cellVertex S (outerSymmetry.edge edge)
        ((outerSymmetry.orientedInner innerSymmetry edge).vertex v) := by
  by_cases horientation : outerSymmetry.respectsOrientation edge
  · have hendpoint := horientation
    change R.endpoint (outerSymmetry.edge edge) = _ at hendpoint
    simp only [orientedInner, horientation, ↓reduceIte, identity, Equiv.refl_apply]
    by_cases hv : v = S.source
    · subst v
      simp only [cellVertex_source, substitutionVertexEquiv, Equiv.sumCongr_apply, Sum.map_inl]
      exact congrArg Sum.inl (congrArg Prod.fst hendpoint).symm
    · by_cases hv' : v = S.target
      · subst v
        simp only [cellVertex_target, substitutionVertexEquiv, Equiv.sumCongr_apply, Sum.map_inl]
        exact congrArg Sum.inl (congrArg Prod.snd hendpoint).symm
      · simp only [cellVertex, hv, hv', ↓reduceDIte]
        change Sum.inr (outerSymmetry.edge edge,
          outerSymmetry.orientedInterior innerSymmetry hs ht edge ⟨v, hv, hv'⟩) = _
        simp [orientedInterior, horientation]
  · have hendpoint : R.endpoint (outerSymmetry.edge edge) =
        (outerSymmetry.vertex (R.endpoint edge).2, outerSymmetry.vertex (R.endpoint edge).1) :=
      (outerSymmetry.endpoint edge).resolve_left horientation
    simp only [orientedInner, horientation, ↓reduceIte]
    by_cases hv : v = S.source
    · subst v
      rw [hs, cellVertex_source, cellVertex_target]
      change Sum.inl (outerSymmetry.vertex (R.endpoint edge).1) = _
      exact congrArg Sum.inl (congrArg Prod.snd hendpoint).symm
    · by_cases hv' : v = S.target
      · subst v
        rw [ht, cellVertex_target, cellVertex_source]
        change Sum.inl (outerSymmetry.vertex (R.endpoint edge).2) = _
        exact congrArg Sum.inl (congrArg Prod.fst hendpoint).symm
      · have hsource : innerSymmetry.vertex v ≠ S.source := by
          intro h; apply hv'; apply innerSymmetry.vertex.injective; exact h.trans ht.symm
        have htarget : innerSymmetry.vertex v ≠ S.target := by
          intro h; apply hv; apply innerSymmetry.vertex.injective; exact h.trans hs.symm
        simp only [cellVertex, hv, hv', hsource, htarget, ↓reduceDIte]
        change Sum.inr (outerSymmetry.edge edge,
          outerSymmetry.orientedInterior innerSymmetry hs ht edge ⟨v, hv, hv'⟩) = _
        simp only [orientedInterior, horientation, ↓reduceIte]
        rfl

def substitute (outerSymmetry : R.NetworkSymmetry) (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source) : (R.substitute S).NetworkSymmetry where
  vertex := (Fintype.equivFin _).symm.trans
    ((outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht).trans (Fintype.equivFin _))
  edge := finProdFinEquiv.symm.trans
    ((outerSymmetry.substitutionEdgeEquiv innerSymmetry).trans finProdFinEquiv)
  endpoint edge := by
    obtain ⟨pair, rfl⟩ := finProdFinEquiv.surjective edge
    rcases pair with ⟨edge, child⟩
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    simp only [substitutionEdgeEquiv_apply, substitute_endpoint, Equiv.symm_apply_apply,
      outerSymmetry.substitutionVertexEquiv_cell innerSymmetry hs ht]
    rcases (outerSymmetry.orientedInner innerSymmetry edge).endpoint child with h | h
    · left; rw [h]
    · right; rw [h]

theorem substitute_source (outerSymmetry : R.NetworkSymmetry) (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source)
    (hsource : outerSymmetry.vertex R.source = R.target) :
    (outerSymmetry.substitute innerSymmetry hs ht).vertex (R.substitute S).source =
      (R.substitute S).target := by
  change Fintype.equivFin _
    (outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl R.source)))) = _
  simp only [Equiv.symm_apply_apply]
  change Fintype.equivFin _ (Sum.inl (outerSymmetry.vertex R.source)) = _
  rw [hsource]
  rfl

theorem substitute_target (outerSymmetry : R.NetworkSymmetry) (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source)
    (htarget : outerSymmetry.vertex R.target = R.source) :
    (outerSymmetry.substitute innerSymmetry hs ht).vertex (R.substitute S).target =
      (R.substitute S).source := by
  change Fintype.equivFin _
    (outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl R.target)))) = _
  simp only [Equiv.symm_apply_apply]
  change Fintype.equivFin _ (Sum.inl (outerSymmetry.vertex R.target)) = _
  rw [htarget]
  rfl

end NetworkSymmetry
end
end Universality.FiniteNetwork
