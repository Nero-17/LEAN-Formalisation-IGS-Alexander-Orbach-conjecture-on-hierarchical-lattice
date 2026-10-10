import Universality.Section5.HeterogeneousFullConnectivity
import Universality.Graph.CanonicalPivotal
import Universality.Graph.SubstitutionConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

theorem heterogeneousCellVertex_eq_forces_same_cell {edge other : Fin outerEdges}
    {inside : Fin (innerVertices edge)} {vertex : Fin (innerVertices other)}
    (hs : inside ≠ (S edge).source) (ht : inside ≠ (S edge).target)
    (heq : R.heterogeneousCellVertex S edge inside =
      R.heterogeneousCellVertex S other vertex) : edge = other := by
  simp only [heterogeneousCellVertex, dif_neg hs, dif_neg ht] at heq
  split_ifs at heq <;> try contradiction
  exact (Sigma.mk.inj_iff.mp (Sum.inr.inj heq)).1

theorem heterogeneousCellEdge_boundary {edge : Fin outerEdges} (child : Fin (innerEdges edge))
    (first : ((S edge).endpoint child).1 = (S edge).source ∨
      ((S edge).endpoint child).1 = (S edge).target)
    (second : ((S edge).endpoint child).2 = (S edge).source ∨
      ((S edge).endpoint child).2 = (S edge).target) :
    s(R.heterogeneousCellVertex S edge ((S edge).endpoint child).1,
      R.heterogeneousCellVertex S edge ((S edge).endpoint child).2) =
      s((Sum.inl (R.endpoint edge).1 : R.HeterogeneousVertex S), Sum.inl (R.endpoint edge).2) := by
  rcases first with first | first <;> rcases second with second | second
  · exact ((S edge).loopless child (first.trans second.symm)).elim
  · rw [first, second, heterogeneousCellVertex_source, heterogeneousCellVertex_target]
    rfl
  · rw [first, second, heterogeneousCellVertex_target, heterogeneousCellVertex_source, Sym2.eq_swap]
    rfl
  · exact ((S edge).loopless child (first.trans second.symm)).elim

/-- Outer simplicity handles even children consisting of one terminal edge. -/
theorem heterogeneousSubstitute_simple
    (outer_simple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (inner_simple : ∀ edge, Function.Injective
      (fun child => s(((S edge).endpoint child).1, ((S edge).endpoint child).2))) :
    Function.Injective (fun edge => s(((R.heterogeneousSubstitute S).endpoint edge).1,
      ((R.heterogeneousSubstitute S).endpoint edge).2)) := by
  intro first second heq
  obtain ⟨⟨edge, child⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective first
  obtain ⟨⟨other, bond⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective second
  simp only [heterogeneousSubstitute_endpoint] at heq
  have mapped :
      s(R.heterogeneousCellVertex S edge ((S edge).endpoint child).1,
        R.heterogeneousCellVertex S edge ((S edge).endpoint child).2) =
      s(R.heterogeneousCellVertex S other ((S other).endpoint bond).1,
        R.heterogeneousCellVertex S other ((S other).endpoint bond).2) := by
    rcases Sym2.eq_iff.mp heq with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨(Fintype.equivFin _).injective hfirst,
        (Fintype.equivFin _).injective hsecond⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨(Fintype.equivFin _).injective hfirst,
        (Fintype.equivFin _).injective hsecond⟩)
  have same_edge : edge = other := by
    by_contra different
    have boundary_first :
        (((S edge).endpoint child).1 = (S edge).source ∨ ((S edge).endpoint child).1 = (S edge).target) ∧
        (((S edge).endpoint child).2 = (S edge).source ∨ ((S edge).endpoint child).2 = (S edge).target) := by
      rcases Sym2.eq_iff.mp mapped with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩ <;>
        constructor <;> by_contra interior <;> push Not at interior
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hfirst)
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hsecond)
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hfirst)
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hsecond)
    have boundary_second :
        (((S other).endpoint bond).1 = (S other).source ∨ ((S other).endpoint bond).1 = (S other).target) ∧
        (((S other).endpoint bond).2 = (S other).source ∨ ((S other).endpoint bond).2 = (S other).target) := by
      rcases Sym2.eq_iff.mp mapped.symm with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩ <;>
        constructor <;> by_contra interior <;> push Not at interior
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hfirst).symm
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hsecond).symm
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hfirst).symm
      · exact different (R.heterogeneousCellVertex_eq_forces_same_cell S interior.1 interior.2 hsecond).symm
    rw [R.heterogeneousCellEdge_boundary S child boundary_first.1 boundary_first.2,
      R.heterogeneousCellEdge_boundary S bond boundary_second.1 boundary_second.2] at mapped
    apply different
    apply outer_simple
    rcases Sym2.eq_iff.mp mapped with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨Sum.inl.inj hfirst, Sum.inl.inj hsecond⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨Sum.inl.inj hfirst, Sum.inl.inj hsecond⟩)
  subst other
  have same_child : child = bond := by
    apply inner_simple edge
    rcases Sym2.eq_iff.mp mapped with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨R.heterogeneousCellVertex_injective S edge hfirst,
        R.heterogeneousCellVertex_injective S edge hsecond⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨R.heterogeneousCellVertex_injective S edge hfirst,
        R.heterogeneousCellVertex_injective S edge hsecond⟩)
  rw [same_child]

theorem heterogeneousSubstitute_cut
    (outer_cut : ∀ edge, R.crosses (onlyClosed edge) = true)
    (inner_connected : ∀ edge, (S edge).fullGraph.Reachable (S edge).source (S edge).target) :
    ∀ edge, (R.heterogeneousSubstitute S).crosses (onlyClosed edge) = true := by
  intro closed
  obtain ⟨⟨edge, child⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective closed
  let cells := (heterogeneousConfigurationEquiv (innerEdges := innerEdges)).symm
    (onlyClosed (Fintype.equivFin _ ⟨edge, child⟩))
  have configuration : heterogeneousConfigurationEquiv cells =
      onlyClosed (Fintype.equivFin _ ⟨edge, child⟩) :=
    (heterogeneousConfigurationEquiv (innerEdges := innerEdges)).apply_symm_apply _
  rw [← configuration, heterogeneousSubstitute_crosses]
  apply R.crosses_mono (onlyClosed edge) _ _ (outer_cut edge)
  intro other opened
  have different : other ≠ edge := by
    intro equality
    subst other
    simp [onlyClosed] at opened
  have other_full : cells other = fun _ => true := by
    funext bond
    change Function.update (fun _ => true)
      (Fintype.equivFin (Σ edge, Fin (innerEdges edge)) ⟨edge, child⟩) false
      (Fintype.equivFin (Σ edge, Fin (innerEdges edge)) ⟨other, bond⟩) = true
    apply Function.update_of_ne
    intro equality
    exact different (congrArg Sigma.fst ((Fintype.equivFin _).injective equality))
  change (S other).crosses (cells other) = true
  rw [other_full]
  exact ((S other).crosses_eq_true _).mpr (inner_connected other)

end
end Universality.FiniteNetwork
