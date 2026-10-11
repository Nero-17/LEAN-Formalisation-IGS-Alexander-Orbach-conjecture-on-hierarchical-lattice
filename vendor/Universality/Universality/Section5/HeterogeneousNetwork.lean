import Universality.Section5.HeterogeneousConnectivity
import Universality.Graph.Rule

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

instance : Fintype (R.HeterogeneousVertex S) := by
  unfold HeterogeneousVertex
  infer_instance

instance : DecidableEq (R.HeterogeneousVertex S) := by
  unfold HeterogeneousVertex
  infer_instance

def heterogeneousSubstitute :
    FiniteNetwork (Fintype.card (R.HeterogeneousVertex S))
      (Fintype.card (Σ edge : Fin outerEdges, Fin (innerEdges edge))) where
  endpoint edge :=
    let child := (Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm edge
    (Fintype.equivFin _ (R.heterogeneousCellVertex S child.1 ((S child.1).endpoint child.2).1),
     Fintype.equivFin _ (R.heterogeneousCellVertex S child.1 ((S child.1).endpoint child.2).2))
  source := Fintype.equivFin _ (Sum.inl R.source)
  target := Fintype.equivFin _ (Sum.inl R.target)
  terminals_distinct := by
    intro equality
    exact R.terminals_distinct (Sum.inl.inj ((Fintype.equivFin _).injective equality))
  loopless edge := by
    intro equality
    exact (S _).loopless _
      (R.heterogeneousCellVertex_injective S _ ((Fintype.equivFin _).injective equality))

def heterogeneousConfigurationEquiv :
    ((edge : Fin outerEdges) → Configuration (innerEdges edge)) ≃
      Configuration (Fintype.card (Σ edge : Fin outerEdges, Fin (innerEdges edge))) where
  toFun configuration edge :=
    let child := (Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm edge
    configuration child.1 child.2
  invFun configuration edge child := configuration (Fintype.equivFin _ ⟨edge, child⟩)
  left_inv configuration := by
    funext edge child
    exact congrArg (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
      configuration pair.1 pair.2) ((Fintype.equivFin _).symm_apply_apply ⟨edge, child⟩)
  right_inv configuration := by
    funext edge
    change configuration (Fintype.equivFin _ ((Fintype.equivFin _).symm edge)) = configuration edge
    rw [Equiv.apply_symm_apply]

theorem heterogeneousConfigurationEquiv_apply
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (edge : Fin outerEdges) (child : Fin (innerEdges edge)) :
    heterogeneousConfigurationEquiv configuration (Fintype.equivFin _ ⟨edge, child⟩) =
      configuration edge child := by
  change (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
      configuration pair.1 pair.2)
      ((Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm
        (Fintype.equivFin _ ⟨edge, child⟩)) = configuration edge child
  exact congrArg (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
    configuration pair.1 pair.2)
    ((Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm_apply_apply ⟨edge, child⟩)

theorem heterogeneousSubstitute_endpoint (edge : Fin outerEdges) (child : Fin (innerEdges edge)) :
    (R.heterogeneousSubstitute S).endpoint (Fintype.equivFin _ ⟨edge, child⟩) =
      (Fintype.equivFin _ (R.heterogeneousCellVertex S edge ((S edge).endpoint child).1),
       Fintype.equivFin _ (R.heterogeneousCellVertex S edge ((S edge).endpoint child).2)) := by
  exact congrArg (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
    (Fintype.equivFin _ (R.heterogeneousCellVertex S pair.1 ((S pair.1).endpoint pair.2).1),
     Fintype.equivFin _ (R.heterogeneousCellVertex S pair.1 ((S pair.1).endpoint pair.2).2)))
    ((Fintype.equivFin _).symm_apply_apply ⟨edge, child⟩)

def heterogeneousGraphIso (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    R.heterogeneousSubstitutedGraph S configuration ≃g
      (R.heterogeneousSubstitute S).openGraph (heterogeneousConfigurationEquiv configuration) where
  toEquiv := Fintype.equivFin _
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨different, edge, opened, endpoints | endpoints⟩
      · let child := (Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm edge
        refine ⟨fun equality => different (congrArg (Fintype.equivFin _) equality),
          child.1, ((S child.1).endpoint child.2).1, ((S child.1).endpoint child.2).2, ?_, ?_, ?_⟩
        · exact ⟨(S child.1).loopless _, _, opened, Or.inl rfl⟩
        · exact (Fintype.equivFin _).injective (congrArg Prod.fst endpoints)
        · exact (Fintype.equivFin _).injective (congrArg Prod.snd endpoints)
      · let child := (Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm edge
        refine ⟨fun equality => different (congrArg (Fintype.equivFin _) equality),
          child.1, ((S child.1).endpoint child.2).2, ((S child.1).endpoint child.2).1, ?_, ?_, ?_⟩
        · exact ⟨((S child.1).loopless _).symm, _, opened, Or.inr rfl⟩
        · exact (Fintype.equivFin _).injective (congrArg Prod.snd endpoints)
        · exact (Fintype.equivFin _).injective (congrArg Prod.fst endpoints)
    · rintro ⟨different, edge, x, y, adjacent, rfl, rfl⟩
      obtain ⟨_, child, opened, endpoints | endpoints⟩ := adjacent
      · refine ⟨fun equality => different ((Fintype.equivFin _).injective equality),
          Fintype.equivFin _ ⟨edge, child⟩, ?_, Or.inl ?_⟩
        · change heterogeneousConfigurationEquiv configuration (Fintype.equivFin _ ⟨edge, child⟩) = true
          rw [heterogeneousConfigurationEquiv_apply]
          exact opened
        · rw [heterogeneousSubstitute_endpoint, endpoints]
      · refine ⟨fun equality => different ((Fintype.equivFin _).injective equality),
          Fintype.equivFin _ ⟨edge, child⟩, ?_, Or.inr ?_⟩
        · change heterogeneousConfigurationEquiv configuration (Fintype.equivFin _ ⟨edge, child⟩) = true
          rw [heterogeneousConfigurationEquiv_apply]
          exact opened
        · rw [heterogeneousSubstitute_endpoint, endpoints]

theorem heterogeneousSubstitute_reachable_iff
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (u v : R.HeterogeneousVertex S) :
    ((R.heterogeneousSubstitute S).openGraph (heterogeneousConfigurationEquiv configuration)).Reachable
      (Fintype.equivFin _ u) (Fintype.equivFin _ v) ↔
      (R.heterogeneousSubstitutedGraph S configuration).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := R.heterogeneousGraphIso S configuration)

theorem heterogeneousSubstitute_crosses
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    (R.heterogeneousSubstitute S).crosses (heterogeneousConfigurationEquiv configuration) =
      R.crosses (heterogeneousCoarseConfiguration S configuration) := by
  apply Bool.eq_iff_iff.mpr
  rw [crosses_eq_true, crosses_eq_true]
  exact (R.heterogeneousSubstitute_reachable_iff S configuration (Sum.inl R.source)
    (Sum.inl R.target)).trans (R.heterogeneousSubstitutedReachable_iff S configuration _ _)

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

def heterogeneousSubstitute (outer : Rule) (children : Fin outer.edges → Rule) : Rule where
  vertices := Fintype.card (outer.network.HeterogeneousVertex (fun edge => (children edge).network))
  edges := Fintype.card (Σ edge : Fin outer.edges, Fin (children edge).edges)
  network := outer.network.heterogeneousSubstitute (fun edge => (children edge).network)

theorem heterogeneousSubstitute_edges (outer : Rule) (children : Fin outer.edges → Rule) :
    (outer.heterogeneousSubstitute children).edges = ∑ edge, (children edge).edges := by
  simp [heterogeneousSubstitute, Fintype.card_sigma]

end
end Universality.Rule
