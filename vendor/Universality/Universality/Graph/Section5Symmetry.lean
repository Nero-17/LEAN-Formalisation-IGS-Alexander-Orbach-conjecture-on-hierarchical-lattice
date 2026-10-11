import Universality.Graph.Section5Canonical
import Universality.Section5.WheatstoneResponse
import Universality.Graph.SubstitutionInvolution

set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork
noncomputable section
variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

theorem heterogeneousCellVertex_interior (edge : Fin outerEdges) (vertex : (S edge).InteriorVertex) :
    R.heterogeneousCellVertex S edge vertex.val = Sum.inr ⟨edge, vertex⟩ := by
  simp [heterogeneousCellVertex, vertex.property.1, vertex.property.2]

def heterogeneousInvolutiveSymmetry
    (vertexFlip : R.HeterogeneousVertex S → R.HeterogeneousVertex S)
    (edgeFlip : (Σ edge, Fin (innerEdges edge)) → (Σ edge, Fin (innerEdges edge)))
    (vertex_involutive : Function.Involutive vertexFlip)
    (edge_involutive : Function.Involutive edgeFlip)
    (endpoint : ∀ pair : Σ edge, Fin (innerEdges edge),
      s(R.heterogeneousCellVertex S (edgeFlip pair).1 ((S (edgeFlip pair).1).endpoint (edgeFlip pair).2).1,
        R.heterogeneousCellVertex S (edgeFlip pair).1 ((S (edgeFlip pair).1).endpoint (edgeFlip pair).2).2) =
      s(vertexFlip (R.heterogeneousCellVertex S pair.1 ((S pair.1).endpoint pair.2).1),
        vertexFlip (R.heterogeneousCellVertex S pair.1 ((S pair.1).endpoint pair.2).2))) :
    (R.heterogeneousSubstitute S).NetworkSymmetry where
  vertex := (Fintype.equivFin _).symm.trans ((vertex_involutive.toPerm vertexFlip).trans (Fintype.equivFin _))
  edge := (Fintype.equivFin _).symm.trans ((edge_involutive.toPerm edgeFlip).trans (Fintype.equivFin _))
  endpoint edge := by
    obtain ⟨⟨edge, child⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective edge
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Function.Involutive.coe_toPerm]
    change (R.heterogeneousSubstitute S).endpoint
        (Fintype.equivFin _ (edgeFlip ⟨edge, child⟩)) = _ ∨ _
    rw [← Sigma.eta (edgeFlip ⟨edge, child⟩), heterogeneousSubstitute_endpoint,
      heterogeneousSubstitute_endpoint]
    simp only [Equiv.symm_apply_apply]
    rcases Sym2.eq_iff.mp (endpoint ⟨edge, child⟩) with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl (Prod.ext (congrArg (Fintype.equivFin _) first) (congrArg (Fintype.equivFin _) second))
    · exact Or.inr (Prod.ext (congrArg (Fintype.equivFin _) first) (congrArg (Fintype.equivFin _) second))

end
end Universality.FiniteNetwork

namespace Universality.Section5
noncomputable section
open FiniteNetwork

/-- The properties required at a child slot; the single edge is allowed. -/
structure TerminalGraphProperties (rule : Rule) : Prop where
  connected : ∀ vertex, rule.network.fullGraph.Reachable rule.network.source vertex
  simple : Function.Injective (fun edge =>
    s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2))
  canonical : ∀ edge, ∃ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
    walk.IsPath ∧ s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) ∈ walk.edges
  symmetric : ∃ symmetry : rule.network.NetworkSymmetry,
    Function.Involutive symmetry.vertex ∧ symmetry.vertex rule.network.source = rule.network.target

structure TerminalInvolution (rule : Rule) where
  symmetry : rule.network.NetworkSymmetry
  vertex_involutive : Function.Involutive symmetry.vertex
  edge_involutive : Function.Involutive symmetry.edge
  source : symmetry.vertex rule.network.source = rule.network.target

theorem TerminalInvolution.target {rule : Rule} (involution : TerminalInvolution rule) :
    involution.symmetry.vertex rule.network.target = rule.network.source := by
  rw [← involution.source]
  exact involution.vertex_involutive _

def TerminalGraphProperties.involution {rule : Rule} (properties : TerminalGraphProperties rule) :
    TerminalInvolution rule :=
  let symmetry := Classical.choose properties.symmetric
  let evidence := Classical.choose_spec properties.symmetric
  ⟨symmetry, evidence.1, symmetry.edge_involutive properties.simple evidence.1, evidence.2⟩

def TerminalInvolution.interior {rule : Rule} (involution : TerminalInvolution rule) :
    rule.network.InteriorVertex ≃ rule.network.InteriorVertex :=
  involution.symmetry.interiorEquiv involution.source involution.target

theorem TerminalInvolution.interior_involutive {rule : Rule} (involution : TerminalInvolution rule) :
    Function.Involutive involution.interior := by
  intro vertex
  apply Subtype.ext
  exact involution.vertex_involutive vertex.val

def wheatstoneInteriorFlip (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    (Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex) →
      (Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex)
  | ⟨edge, vertex⟩ =>
      Fin.cases (fun vertex => ⟨3, first.interior vertex⟩)
        (Fin.cases (fun vertex => ⟨2, second.interior vertex⟩)
          (Fin.cases (fun vertex => ⟨1, second.interior vertex⟩)
            (Fin.cases (fun vertex => ⟨0, first.interior vertex⟩)
              (Fin.cases (fun vertex => ⟨4, central.interior vertex⟩)
                (fun edge => Fin.elim0 edge))))) edge vertex

def wheatstoneVertexFlip (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    wheatstoneNetwork.HeterogeneousVertex (fun edge => (![a,b,b,a,c] edge).network) →
      wheatstoneNetwork.HeterogeneousVertex (fun edge => (![a,b,b,a,c] edge).network) :=
  Sum.map (![1,0,3,2]) (wheatstoneInteriorFlip a b c first second central)

def wheatstoneEdgeFlip (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    (Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges) →
      (Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges)
  | ⟨edge, child⟩ =>
      Fin.cases (fun child => ⟨3, first.symmetry.edge child⟩)
        (Fin.cases (fun child => ⟨2, second.symmetry.edge child⟩)
          (Fin.cases (fun child => ⟨1, second.symmetry.edge child⟩)
            (Fin.cases (fun child => ⟨0, first.symmetry.edge child⟩)
              (Fin.cases (fun child => ⟨4, central.symmetry.edge child⟩)
                (fun edge => Fin.elim0 edge))))) edge child

theorem wheatstoneInteriorFlip_involutive (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    Function.Involutive (wheatstoneInteriorFlip a b c first second central) := by
  rintro ⟨edge, vertex⟩
  fin_cases edge
  · exact congrArg (fun vertex : a.network.InteriorVertex =>
      (⟨0, vertex⟩ : Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex))
      (first.interior_involutive vertex)
  · exact congrArg (fun vertex : b.network.InteriorVertex =>
      (⟨1, vertex⟩ : Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex))
      (second.interior_involutive vertex)
  · exact congrArg (fun vertex : b.network.InteriorVertex =>
      (⟨2, vertex⟩ : Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex))
      (second.interior_involutive vertex)
  · exact congrArg (fun vertex : a.network.InteriorVertex =>
      (⟨3, vertex⟩ : Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex))
      (first.interior_involutive vertex)
  · exact congrArg (fun vertex : c.network.InteriorVertex =>
      (⟨4, vertex⟩ : Σ edge : Fin 5, (![a,b,b,a,c] edge).network.InteriorVertex))
      (central.interior_involutive vertex)

theorem wheatstoneVertexFlip_involutive (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    Function.Involutive (wheatstoneVertexFlip a b c first second central) := by
  intro vertex
  cases vertex with
  | inl vertex => fin_cases vertex <;> rfl
  | inr vertex => exact congrArg Sum.inr (wheatstoneInteriorFlip_involutive a b c first second central vertex)

theorem wheatstoneEdgeFlip_involutive (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    Function.Involutive (wheatstoneEdgeFlip a b c first second central) := by
  rintro ⟨edge, child⟩
  fin_cases edge
  · exact congrArg (fun child : Fin a.edges => (⟨0, child⟩ : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges))
      (first.edge_involutive child)
  · exact congrArg (fun child : Fin b.edges => (⟨1, child⟩ : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges))
      (second.edge_involutive child)
  · exact congrArg (fun child : Fin b.edges => (⟨2, child⟩ : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges))
      (second.edge_involutive child)
  · exact congrArg (fun child : Fin a.edges => (⟨3, child⟩ : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges))
      (first.edge_involutive child)
  · exact congrArg (fun child : Fin c.edges => (⟨4, child⟩ : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges))
      (central.edge_involutive child)

theorem wheatstoneVertexFlip_cell_0 (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (vertex : Fin a.vertices) :
    wheatstoneVertexFlip a b c first second central
      (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 0 vertex) =
    wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 3
      (first.symmetry.vertex vertex) := by
  by_cases source : vertex = a.network.source
  · subst vertex
    erw [heterogeneousCellVertex_source, first.source, heterogeneousCellVertex_target]
    rfl
  · by_cases target : vertex = a.network.target
    · subst vertex
      erw [heterogeneousCellVertex_target, first.target, heterogeneousCellVertex_source]
      rfl
    · rw [show wheatstoneNetwork.heterogeneousCellVertex
          (fun edge => (![a,b,b,a,c] edge).network) 0 vertex =
          Sum.inr ⟨0, ⟨vertex, source, target⟩⟩ from
          wheatstoneNetwork.heterogeneousCellVertex_interior
            (fun edge => (![a,b,b,a,c] edge).network) 0 ⟨vertex, source, target⟩]
      exact (wheatstoneNetwork.heterogeneousCellVertex_interior
        (fun edge => (![a,b,b,a,c] edge).network) 3
        (first.interior ⟨vertex, source, target⟩)).symm

theorem wheatstoneVertexFlip_cell_1 (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (vertex : Fin b.vertices) :
    wheatstoneVertexFlip a b c first second central
      (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 1 vertex) =
    wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 2
      (second.symmetry.vertex vertex) := by
  by_cases source : vertex = b.network.source
  · subst vertex
    erw [heterogeneousCellVertex_source, second.source, heterogeneousCellVertex_target]
    rfl
  · by_cases target : vertex = b.network.target
    · subst vertex
      erw [heterogeneousCellVertex_target, second.target, heterogeneousCellVertex_source]
      rfl
    · rw [show wheatstoneNetwork.heterogeneousCellVertex
          (fun edge => (![a,b,b,a,c] edge).network) 1 vertex =
          Sum.inr ⟨1, ⟨vertex, source, target⟩⟩ from
          wheatstoneNetwork.heterogeneousCellVertex_interior
            (fun edge => (![a,b,b,a,c] edge).network) 1 ⟨vertex, source, target⟩]
      exact (wheatstoneNetwork.heterogeneousCellVertex_interior
        (fun edge => (![a,b,b,a,c] edge).network) 2
        (second.interior ⟨vertex, source, target⟩)).symm

theorem wheatstoneVertexFlip_cell_2 (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (vertex : Fin b.vertices) :
    wheatstoneVertexFlip a b c first second central
      (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 2 vertex) =
    wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 1
      (second.symmetry.vertex vertex) := by
  by_cases source : vertex = b.network.source
  · subst vertex
    erw [heterogeneousCellVertex_source, second.source, heterogeneousCellVertex_target]
    rfl
  · by_cases target : vertex = b.network.target
    · subst vertex
      erw [heterogeneousCellVertex_target, second.target, heterogeneousCellVertex_source]
      rfl
    · rw [show wheatstoneNetwork.heterogeneousCellVertex
          (fun edge => (![a,b,b,a,c] edge).network) 2 vertex =
          Sum.inr ⟨2, ⟨vertex, source, target⟩⟩ from
          wheatstoneNetwork.heterogeneousCellVertex_interior
            (fun edge => (![a,b,b,a,c] edge).network) 2 ⟨vertex, source, target⟩]
      exact (wheatstoneNetwork.heterogeneousCellVertex_interior
        (fun edge => (![a,b,b,a,c] edge).network) 1
        (second.interior ⟨vertex, source, target⟩)).symm

theorem wheatstoneVertexFlip_cell_3 (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (vertex : Fin a.vertices) :
    wheatstoneVertexFlip a b c first second central
      (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 3 vertex) =
    wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 0
      (first.symmetry.vertex vertex) := by
  by_cases source : vertex = a.network.source
  · subst vertex
    erw [heterogeneousCellVertex_source, first.source, heterogeneousCellVertex_target]
    rfl
  · by_cases target : vertex = a.network.target
    · subst vertex
      erw [heterogeneousCellVertex_target, first.target, heterogeneousCellVertex_source]
      rfl
    · rw [show wheatstoneNetwork.heterogeneousCellVertex
          (fun edge => (![a,b,b,a,c] edge).network) 3 vertex =
          Sum.inr ⟨3, ⟨vertex, source, target⟩⟩ from
          wheatstoneNetwork.heterogeneousCellVertex_interior
            (fun edge => (![a,b,b,a,c] edge).network) 3 ⟨vertex, source, target⟩]
      exact (wheatstoneNetwork.heterogeneousCellVertex_interior
        (fun edge => (![a,b,b,a,c] edge).network) 0
        (first.interior ⟨vertex, source, target⟩)).symm

theorem wheatstoneVertexFlip_cell_4 (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (vertex : Fin c.vertices) :
    wheatstoneVertexFlip a b c first second central
      (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 4 vertex) =
    wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network) 4
      (central.symmetry.vertex vertex) := by
  by_cases source : vertex = c.network.source
  · subst vertex
    erw [heterogeneousCellVertex_source, central.source, heterogeneousCellVertex_target]
    rfl
  · by_cases target : vertex = c.network.target
    · subst vertex
      erw [heterogeneousCellVertex_target, central.target, heterogeneousCellVertex_source]
      rfl
    · rw [show wheatstoneNetwork.heterogeneousCellVertex
          (fun edge => (![a,b,b,a,c] edge).network) 4 vertex =
          Sum.inr ⟨4, ⟨vertex, source, target⟩⟩ from
          wheatstoneNetwork.heterogeneousCellVertex_interior
            (fun edge => (![a,b,b,a,c] edge).network) 4 ⟨vertex, source, target⟩]
      exact (wheatstoneNetwork.heterogeneousCellVertex_interior
        (fun edge => (![a,b,b,a,c] edge).network) 4
        (central.interior ⟨vertex, source, target⟩)).symm

theorem wheatstoneFlip_endpoint (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c)
    (pair : Σ edge : Fin 5, Fin (![a,b,b,a,c] edge).edges) :
    s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        (wheatstoneEdgeFlip a b c first second central pair).1
        ((![a,b,b,a,c] (wheatstoneEdgeFlip a b c first second central pair).1).network.endpoint
          (wheatstoneEdgeFlip a b c first second central pair).2).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        (wheatstoneEdgeFlip a b c first second central pair).1
        ((![a,b,b,a,c] (wheatstoneEdgeFlip a b c first second central pair).1).network.endpoint
          (wheatstoneEdgeFlip a b c first second central pair).2).2) =
    s(wheatstoneVertexFlip a b c first second central
        (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
          pair.1 ((![a,b,b,a,c] pair.1).network.endpoint pair.2).1),
      wheatstoneVertexFlip a b c first second central
        (wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
          pair.1 ((![a,b,b,a,c] pair.1).network.endpoint pair.2).2)) := by
  rcases pair with ⟨edge, child⟩
  fin_cases edge
  · change s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        3 (a.network.endpoint (first.symmetry.edge child)).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        3 (a.network.endpoint (first.symmetry.edge child)).2) = _
    erw [wheatstoneVertexFlip_cell_0, wheatstoneVertexFlip_cell_0]
    rcases first.symmetry.endpoint child with endpoints | endpoints
    · rw [endpoints]
      rfl
    · rw [endpoints]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · change s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        2 (b.network.endpoint (second.symmetry.edge child)).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        2 (b.network.endpoint (second.symmetry.edge child)).2) = _
    erw [wheatstoneVertexFlip_cell_1, wheatstoneVertexFlip_cell_1]
    rcases second.symmetry.endpoint child with endpoints | endpoints
    · rw [endpoints]
      rfl
    · rw [endpoints]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · change s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        1 (b.network.endpoint (second.symmetry.edge child)).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        1 (b.network.endpoint (second.symmetry.edge child)).2) = _
    erw [wheatstoneVertexFlip_cell_2, wheatstoneVertexFlip_cell_2]
    rcases second.symmetry.endpoint child with endpoints | endpoints
    · rw [endpoints]
      rfl
    · rw [endpoints]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · change s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        0 (a.network.endpoint (first.symmetry.edge child)).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        0 (a.network.endpoint (first.symmetry.edge child)).2) = _
    erw [wheatstoneVertexFlip_cell_3, wheatstoneVertexFlip_cell_3]
    rcases first.symmetry.endpoint child with endpoints | endpoints
    · rw [endpoints]
      rfl
    · rw [endpoints]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · change s(wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        4 (c.network.endpoint (central.symmetry.edge child)).1,
      wheatstoneNetwork.heterogeneousCellVertex (fun edge => (![a,b,b,a,c] edge).network)
        4 (c.network.endpoint (central.symmetry.edge child)).2) = _
    erw [wheatstoneVertexFlip_cell_4, wheatstoneVertexFlip_cell_4]
    rcases central.symmetry.endpoint child with endpoints | endpoints
    · rw [endpoints]
      rfl
    · rw [endpoints]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

def wheatstoneTerminalInvolution (a b c : Rule)
    (first : TerminalInvolution a) (second : TerminalInvolution b) (central : TerminalInvolution c) :
    TerminalInvolution (wheatstoneRule a b c) where
  symmetry := wheatstoneNetwork.heterogeneousInvolutiveSymmetry
    (fun edge => (![a,b,b,a,c] edge).network)
    (wheatstoneVertexFlip a b c first second central)
    (wheatstoneEdgeFlip a b c first second central)
    (wheatstoneVertexFlip_involutive a b c first second central)
    (wheatstoneEdgeFlip_involutive a b c first second central)
    (wheatstoneFlip_endpoint a b c first second central)
  vertex_involutive := by
    intro vertex
    change Fintype.equivFin _
      (wheatstoneVertexFlip a b c first second central
        ((Fintype.equivFin _).symm (Fintype.equivFin _
          (wheatstoneVertexFlip a b c first second central ((Fintype.equivFin _).symm vertex))))) = vertex
    rw [Equiv.symm_apply_apply, wheatstoneVertexFlip_involutive, Equiv.apply_symm_apply]
  edge_involutive := by
    intro edge
    change Fintype.equivFin _
      (wheatstoneEdgeFlip a b c first second central
        ((Fintype.equivFin _).symm (Fintype.equivFin _
          (wheatstoneEdgeFlip a b c first second central ((Fintype.equivFin _).symm edge))))) = edge
    rw [Equiv.symm_apply_apply, wheatstoneEdgeFlip_involutive, Equiv.apply_symm_apply]
  source := by
    change Fintype.equivFin _
      (wheatstoneVertexFlip a b c first second central
        ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl 0)))) =
      Fintype.equivFin _ (Sum.inl 1)
    rw [Equiv.symm_apply_apply]
    rfl

end
end Universality.Section5
