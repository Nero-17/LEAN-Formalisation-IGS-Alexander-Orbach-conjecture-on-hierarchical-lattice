import IGSIII.Chemical.SubstitutionPaths.IndexedPaths
import IGSIII.Chemical.PathBounds
import Universality.Percolation.ConditionalPivotal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Actual pivotal edges are the edges common to all terminal paths

Closing an avoided indexed edge preserves the whole terminal walk. Conversely
a terminal path in the closed configuration remains a terminal path in the
original configuration. These pathwise facts identify the manuscript's common
edge count with the existing IGS II conditional pivotal count.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem edgePathFamily_mono {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (first second : Configuration edges)
    (opening : ∀ edge, first edge = true → second edge = true)
    (crossing : network.crosses first = true) :
    (edgePathFamily network first).paths ⊆ (edgePathFamily network second).paths := by
  classical
  have firstReachable := (network.crosses_eq_true _).mp crossing
  have secondReachable := (network.crosses_eq_true _).mp (network.crosses_mono first second opening crossing)
  have inclusion : network.openGraph first ≤ network.openGraph second := by
    intro source target adjacent
    obtain ⟨distinct, edge, retained, endpoints⟩ := adjacent
    exact ⟨distinct, edge, opening edge retained, endpoints⟩
  intro path membership
  simp only [edgePathFamily, dif_pos firstReachable] at membership
  simp only [edgePathFamily, dif_pos secondReachable]
  obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
  obtain ⟨walk, simple, rfl⟩ :=
    (mem_graphPathFamily _ network.source network.target firstReachable bondPath).mp bondMembership
  apply Finset.mem_image.mpr
  refine ⟨walk.edges.toFinset, ?_, rfl⟩
  exact (mem_graphPathFamily _ network.source network.target secondReachable _).mpr
    ⟨walk.mapLe inclusion, simple.mapLe inclusion, by simp⟩

theorem edgePathFamily_avoiding_edge_crosses {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crossing : network.crosses configuration = true) {path : Finset (Fin edges)}
    (membership : path ∈ (edgePathFamily network configuration).paths) (edge : Fin edges)
    (avoided : edge ∉ path) :
    network.crosses (Function.update configuration edge false) = true := by
  classical
  have reachable := (network.crosses_eq_true _).mp crossing
  simp only [edgePathFamily, dif_pos reachable] at membership
  obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
  obtain ⟨walk, _, rfl⟩ :=
    (mem_graphPathFamily _ network.source network.target reachable bondPath).mp bondMembership
  have avoidedBond : s((network.endpoint edge).1, (network.endpoint edge).2) ∉ walk.edges.toFinset := by
    intro bondMembership
    exact avoided (Finset.mem_filter.mpr ⟨Finset.mem_univ edge, bondMembership⟩)
  apply (network.crosses_eq_true _).mpr
  refine ⟨walk.transfer (network.openGraph (Function.update configuration edge false)) ?_⟩
  intro bond bondMembership
  revert bondMembership
  refine Sym2.inductionOn bond (fun source target bondMembership => ?_)
  obtain ⟨distinct, other, retained, endpoints | endpoints⟩ := walk.adj_of_mem_edges bondMembership
  · have different : other ≠ edge := by
      intro same
      subst other
      apply avoidedBond
      rw [endpoints]
      exact List.mem_toFinset.mpr bondMembership
    exact ⟨distinct, other, by simpa [Function.update_of_ne different] using retained, Or.inl endpoints⟩
  · have different : other ≠ edge := by
      intro same
      subst other
      apply avoidedBond
      rw [endpoints, Sym2.eq_swap]
      exact List.mem_toFinset.mpr bondMembership
    exact ⟨distinct, other, by simpa [Function.update_of_ne different] using retained, Or.inr endpoints⟩

theorem edgePathFamily_commonEdges_eq_pivotal {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    (edgePathFamily network configuration).commonEdges =
      Finset.univ.filter (fun edge => network.pivotal configuration edge = true) := by
  classical
  ext edge
  simp only [PathFamily.commonEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  have openingCrosses : network.crosses (Function.update configuration edge true) = true := by
    apply network.crosses_mono configuration _ _ crossing
    intro other retained
    by_cases same : other = edge
    · subst other; simp
    · simpa [Function.update_of_ne same] using retained
  constructor
  · intro common
    have closingDoesNotCross : network.crosses (Function.update configuration edge false) = false := by
      cases closingCrosses : network.crosses (Function.update configuration edge false) with
      | false => rfl
      | true =>
          obtain ⟨path, membership⟩ := (edgePathFamily network (Function.update configuration edge false)).nonempty
          have originalMembership := edgePathFamily_mono network
            (Function.update configuration edge false) configuration
              (by
                intro other retained
                by_cases same : other = edge
                · subst other; simp at retained
                · simpa [Function.update_of_ne same] using retained) closingCrosses membership
          have retained := edgePathFamily_used_edge network simple (Function.update configuration edge false)
            membership (common path originalMembership)
          simp at retained
    simp only [FiniteNetwork.pivotal, openingCrosses, closingDoesNotCross, Bool.not_false, Bool.and_self]
  · intro pivotal path membership
    by_contra avoided
    have closingCrosses := edgePathFamily_avoiding_edge_crosses network configuration crossing membership edge avoided
    simp only [FiniteNetwork.pivotal, openingCrosses, closingCrosses, Bool.not_true, Bool.true_and] at pivotal
    contradiction

theorem edgePathFamily_commonEdges_card_eq_pivotalCount {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    (edgePathFamily network configuration).commonEdges.card = network.pivotalCount configuration := by
  rw [edgePathFamily_commonEdges_eq_pivotal network simple configuration crossing]
  rfl

/-- The common-edge mean under the actual connected rule law is precisely
the reliability derivative at the fixed point. -/
theorem conditioned_commonEdges_mean_eq_reliability_deriv {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (fixedPoint : network.reliability p = p) :
    (∑ configuration : Configuration edges,
      network.conditionalCellWeight p true configuration *
        ((edgePathFamily network configuration).commonEdges.card : ℝ)) = deriv network.reliability p := by
  classical
  calc
    _ = ∑ configuration : Configuration edges,
        network.conditionalCellWeight p true configuration * (network.pivotalCount configuration : ℝ) := by
      apply Finset.sum_congr rfl
      intro configuration _
      by_cases crossing : network.crosses configuration = true
      · rw [edgePathFamily_commonEdges_card_eq_pivotalCount network simple configuration crossing]
      · simp [FiniteNetwork.conditionalCellWeight, crossing]
    _ = expectation p (fun configuration => if network.crosses configuration then
        (network.pivotalCount configuration : ℝ) else 0) / network.reliability p := by
      rw [FiniteNetwork.expectation, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro configuration _
      cases crossing : network.crosses configuration <;>
        simp [FiniteNetwork.conditionalCellWeight, crossing, div_mul_eq_mul_div]
    _ = _ := network.conditional_connected_pivotalCount_at_fixed_point p fixedPoint (ne_of_gt positive)

end IGSIII.Chemical.Substitution
