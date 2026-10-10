import Universality.Percolation.BirthRadiusRecursion
import Universality.Percolation.CoarseRootLaw
import Universality.Percolation.ConditionalSubstitutionLaw
import Universality.Percolation.SimpleConfigurations
import Universality.Graph.SubstitutionFullConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- On a one-open-edge coarse configuration whose two endpoints are
internal, the crossing child cluster is a birth cluster. Every vertex in
that cluster has radius at least half the child's terminal distance. -/
theorem birthRadiusRootCount_ge_onlyOpen_mass
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges)
    (hfirstSource : (R.endpoint edge).1 ≠ R.source)
    (hfirstTarget : (R.endpoint edge).1 ≠ R.target)
    (hsecondSource : (R.endpoint edge).2 ≠ R.source)
    (hsecondTarget : (R.endpoint edge).2 ≠ R.target)
    (cells : Fin outerEdges → Configuration innerEdges)
    (hcoarse : S.coarseConfiguration cells = onlyOpen edge)
    (radius : ℕ) (hradius : 2 * radius ≤ S.fullGraph.dist S.source S.target) :
    S.internalSelectedMass true false (cells edge) ≤ R.birthRadiusRootCount S cells radius := by
  let first := R.cellEmbedding S edge S.source
  let second := R.cellEmbedding S edge S.target
  let cluster := (R.substitute S).clusterVertices (substitutionConfigurationEquiv cells) first
  have hfirstCoarse : first = Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).1) := by
    change Fintype.equivFin _ (R.cellVertex S edge S.source) = _
    rw [R.cellVertex_source]
  have hcrossing : S.crosses (cells edge) = true := by
    have heq := congrFun hcoarse edge
    simpa only [coarseConfiguration, onlyOpen, Function.update_self] using heq
  have hclusterBirth : cluster ∈ R.birthClusterFamily S cells := by
    dsimp only [cluster]
    rw [hfirstCoarse, R.coarseRoot_cluster_mem_birth_iff S, hcoarse]
    simp only [mem_clusterVertices, R.reachable_onlyOpen_iff]
    simp [hfirstSource, hfirstTarget, hsecondSource, hsecondTarget]
  have hfirst : first ∈ cluster := (R.substitute S).root_mem_clusterVertices _ _
  have hsecond : second ∈ cluster := by
    apply ((R.substitute S).mem_clusterVertices _ _ _).mpr
    change ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin _ (R.cellVertex S edge S.source))
      (Fintype.equivFin _ (R.cellVertex S edge S.target))
    rw [R.substitute_reachable_iff S]
    exact ((S.crosses_eq_true _).mp hcrossing).map (R.cellHom S cells edge)
  have hdistance : (R.substitute S).fullGraph.dist first second = S.fullGraph.dist S.source S.target :=
    R.substitute_cell_distance S hinner edge S.source S.target
  have hcount : (R.substitute S).clusterRadiusRootCount cluster radius = cluster.card := by
    unfold clusterRadiusRootCount
    congr 1
    apply Finset.filter_eq_self.mpr
    intro root hroot
    have hconnected : (R.substitute S).fullGraph.Reachable first root :=
      (R.substitute_all_vertices_connected S houter hinner first).symm.trans
        (R.substitute_all_vertices_connected S houter hinner root)
    have hbound := (R.substitute S).dist_le_twice_clusterRadius cluster root first second
      hfirst hsecond hconnected
    rw [hdistance] at hbound
    omega
  have hsource : (R.openGraph (onlyOpen edge)).reachableDecide (R.endpoint edge).1 (R.endpoint edge).1 = true := by
    exact ((R.openGraph (onlyOpen edge)).reachableDecide_eq_true _ _).mpr (.refl _)
  have htarget : (R.openGraph (onlyOpen edge)).reachableDecide (R.endpoint edge).1 (R.endpoint edge).2 = true := by
    apply ((R.openGraph (onlyOpen edge)).reachableDecide_eq_true _ _).mpr
    exact (R.reachable_onlyOpen_iff edge _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hstate : R.rootChildState (R.endpoint edge).1 (onlyOpen edge) edge = .connected := by
    unfold rootChildState
    rw [hsource, htarget]
    simp [onlyOpen, orientedStateOf]
  have hmass : S.internalSelectedMass true false (cells edge) ≤ cluster.card := by
    have hformula := R.coarseRoot_cluster_mass S cells (R.endpoint edge).1
    have hterm : S.internalStateMass
        (R.rootChildState (R.endpoint edge).1 (S.coarseConfiguration cells) edge) (cells edge) ≤
        ∑ other, S.internalStateMass
          (R.rootChildState (R.endpoint edge).1 (S.coarseConfiguration cells) other) (cells other) :=
      Finset.single_le_sum (f := fun other => S.internalStateMass
        (R.rootChildState (R.endpoint edge).1 (S.coarseConfiguration cells) other) (cells other))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ edge)
    rw [hcoarse, hstate] at hterm
    have hselected : S.internalSelectedMass true false (cells edge) ≤ S.internalStateMass .connected (cells edge) := by
      simp only [internalStateMass, internalSelectedMass]
      apply Finset.sum_le_sum
      intro vertex _
      simp only [OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive,
        Bool.true_and, Bool.false_and, Bool.or_false]
      cases (S.openGraph (cells edge)).reachableDecide S.source vertex.val <;>
        cases (S.openGraph (cells edge)).reachableDecide S.target vertex.val <;> decide
    dsimp only [cluster]
    rw [hfirstCoarse, hformula, hcoarse]
    exact (hselected.trans hterm).trans (Nat.le_add_left _ _)
  have hterm : (R.substitute S).clusterRadiusRootCount cluster radius ≤ R.birthRadiusRootCount S cells radius :=
    Finset.single_le_sum (f := fun cluster => (R.substitute S).clusterRadiusRootCount cluster radius)
      (fun _ _ => Nat.zero_le _) hclusterBirth
  rw [hcount] at hterm
  exact hmass.trans hterm

/-- The one-open-edge branch gives an actual Bernoulli expectation lower
bound, retaining only the connected child's internal mass. -/
theorem expectedBirthRadiusRootCount_ge_onlyOpen_mass
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (edge : Fin outerEdges)
    (hfirstSource : (R.endpoint edge).1 ≠ R.source)
    (hfirstTarget : (R.endpoint edge).1 ≠ R.target)
    (hsecondSource : (R.endpoint edge).2 ≠ R.source)
    (hsecondTarget : (R.endpoint edge).2 ≠ R.target)
    (radius : ℕ) (hradius : 2 * radius ≤ S.fullGraph.dist S.source S.target) :
    bernoulliWeight (S.reliability p) (onlyOpen edge) * S.conditionalVertexMass p .connected ≤
      R.expectedBirthRadiusRootCount S p radius := by
  let count (cells : Fin outerEdges → Configuration innerEdges) : ℝ := R.birthRadiusRootCount S cells radius
  have hdisintegration : R.expectedBirthRadiusRootCount S p radius =
      ∑ coarse : Configuration outerEdges, bernoulliWeight (S.reliability p) coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ other, S.conditionalCellWeight p (coarse other) (cells other)) * count cells := by
    unfold expectedBirthRadiusRootCount
    rw [← substitutionConfigurationEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, bernoulliWeight_substitutionConfiguration]
    exact S.coarse_substitution_observable p hpositive hless (fun _ cells => count cells)
  rw [hdisintegration]
  have hpoint (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ other, S.conditionalCellWeight p (onlyOpen edge other) (cells other)) *
          (S.internalSelectedMass true false (cells edge) : ℝ) ≤
        (∏ other, S.conditionalCellWeight p (onlyOpen edge other) (cells other)) * count cells := by
    by_cases hconsistent : ∀ other, S.crosses (cells other) = onlyOpen edge other
    · apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg (fun _ _ => S.conditionalCellWeight_nonneg hp hp' _ _))
      dsimp only [count]
      exact_mod_cast R.birthRadiusRootCount_ge_onlyOpen_mass S houter hinner edge
        hfirstSource hfirstTarget hsecondSource hsecondTarget cells (funext hconsistent) radius hradius
    · obtain ⟨other, hother⟩ := not_forall.mp hconsistent
      have hzero : (∏ other, S.conditionalCellWeight p (onlyOpen edge other) (cells other)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ other)
        simp [conditionalCellWeight, hother]
      simp only [hzero, zero_mul, le_refl]
  have hconditional : S.conditionalVertexMass p .connected ≤
      ∑ cells : Fin outerEdges → Configuration innerEdges,
        (∏ other, S.conditionalCellWeight p (onlyOpen edge other) (cells other)) * count cells := by
    have hmoment := S.conditional_product_cell_moment p hpositive hless (onlyOpen edge) edge
      (fun cell => (S.internalSelectedMass true false cell : ℝ))
    have hmean : S.conditionalVertexMass p .connected =
        ∑ cell, S.conditionalCellWeight p true cell * (S.internalSelectedMass true false cell : ℝ) := rfl
    simp only [onlyOpen, Function.update_self] at hmoment
    rw [hmean, ← hmoment]
    exact Finset.sum_le_sum (fun cells _ => hpoint cells)
  have hnonnegative (coarse : Configuration outerEdges) :
      0 ≤ bernoulliWeight (S.reliability p) coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ other, S.conditionalCellWeight p (coarse other) (cells other)) * count cells := by
    apply mul_nonneg (bernoulliWeight_nonneg hpositive.le hless.le _)
    apply Finset.sum_nonneg
    intro cells _
    exact mul_nonneg (Finset.prod_nonneg (fun _ _ => S.conditionalCellWeight_nonneg hp hp' _ _))
      (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left hconditional (bernoulliWeight_nonneg hpositive.le hless.le _)).trans
    (Finset.single_le_sum (fun coarse _ => hnonnegative coarse) (Finset.mem_univ (onlyOpen edge)))

end
end Universality.FiniteNetwork
