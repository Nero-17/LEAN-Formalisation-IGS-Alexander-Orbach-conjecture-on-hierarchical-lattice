import IGSIII.Geometry.FiniteSkeleton
import IGSIII.Geometry.ActualComponentRadius

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution Filter
open scoped Topology

variable {vertices edges : ℕ}

/-- Assign the given indexed cell length to its unordered coarse bond. -/
noncomputable def indexedBondCost (network : FiniteNetwork vertices edges) (values : Fin edges → ℝ)
    (bond : Sym2 (Fin vertices)) : ℝ := by
  classical
  exact if exists_edge : ∃ edge, s((network.endpoint edge).1, (network.endpoint edge).2) = bond then
    values (Classical.choose exists_edge) else 0

theorem indexedBondCost_endpoint (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (values : Fin edges → ℝ) (edge : Fin edges) :
    indexedBondCost network values s((network.endpoint edge).1, (network.endpoint edge).2) = values edge := by
  have exists_edge : ∃ other, s((network.endpoint other).1, (network.endpoint other).2) =
      s((network.endpoint edge).1, (network.endpoint edge).2) := ⟨edge, rfl⟩
  simp only [indexedBondCost, dif_pos exists_edge]
  rw [simple (Classical.choose_spec exists_edge)]

theorem indexedBondCost_nonnegative (network : FiniteNetwork vertices edges)
    (values : Fin edges → ℝ) (nonnegative : ∀ edge, 0 ≤ values edge) :
    ∀ bond, 0 ≤ indexedBondCost network values bond := by
  intro bond
  unfold indexedBondCost
  split_ifs
  · exact nonnegative _
  · exact le_rfl

theorem indexedBondCost_positive_on_open_edges (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (values : Fin edges → ℝ)
    (positive : ∀ edge, configuration edge = true → 0 < values edge) :
    ∀ bond ∈ (network.openGraph configuration).edgeSet, 0 < indexedBondCost network values bond := by
  intro bond
  refine Sym2.inductionOn bond (fun first second => ?_)
  intro adjacent
  change (network.openGraph configuration).Adj first second at adjacent
  obtain ⟨_, edge, opened, endpoints | endpoints⟩ := adjacent
  · have bond_identity : s((network.endpoint edge).1, (network.endpoint edge).2) = s(first, second) := by rw [endpoints]
    rw [← bond_identity, indexedBondCost_endpoint network simple]
    exact positive edge opened
  · have bond_identity : s((network.endpoint edge).1, (network.endpoint edge).2) = s(first, second) := by
      rw [endpoints, Sym2.eq_swap]
    rw [← bond_identity, indexedBondCost_endpoint network simple]
    exact positive edge opened

def RetainedSkeletonVertex (network : FiniteNetwork vertices edges) (configuration : Configuration edges) :=
  {vertex : Fin vertices // (network.openGraph configuration).Reachable network.source vertex}

/-- The finite skeleton metric is constructed from actual shortest paths on
the retained coarse component. Its metric axioms and strict separation follow
from positive connected-cell lengths. -/
@[reducible] noncomputable def actualSkeletonMetric (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (values : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ values edge)
    (positive : ∀ edge, configuration edge = true → 0 < values edge) :
    MetricSpace (RetainedSkeletonVertex network configuration) where
  dist first second := weightedDistance (network.openGraph configuration) (indexedBondCost network values) first.val second.val
  dist_self first := weightedDistance_self _ _ (indexedBondCost_nonnegative network values nonnegative) first.val
  dist_comm first second := weightedDistance_comm _ _ (indexedBondCost_nonnegative network values nonnegative) first.val second.val
  dist_triangle first middle last := weightedDistance_triangle _ _ (indexedBondCost_nonnegative network values nonnegative)
    (first.property.symm.trans middle.property) (middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := fun {first second} zero_distance => Subtype.ext
    (eq_of_weightedDistance_eq_zero_of_edge_positive _ _ (indexedBondCost_nonnegative network values nonnegative)
      (indexedBondCost_positive_on_open_edges network simple configuration values positive)
      (first.property.symm.trans second.property) zero_distance)

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Compressing and expanding actual microscopic paths gives the exact
restricted metric, with dangling one-attachment excursions removed by the
proved finite substitution min-plus identity. -/
theorem actual_skeleton_restricted_distance_eq (outer : FiniteNetwork outerVertices outerEdges)
    (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (cells : Fin outerEdges → Configuration innerEdges) (coarse : Configuration outerEdges)
    (coarsens : inner.coarseConfiguration cells = coarse)
    (scalar : ℝ) (scalar_nonnegative : 0 ≤ scalar)
    {first last : Fin outerVertices} (reachable : (outer.openGraph coarse).Reachable first last) :
    scalar * (((outer.substitute inner).openGraph (substitutionConfigurationEquiv cells)).dist
      (Fintype.equivFin _ (Sum.inl first)) (Fintype.equivFin _ (Sum.inl last)) : ℝ) =
      weightedDistance (outer.openGraph coarse)
        (fun bond => scalar * (childDistanceCost outer inner cells bond : ℝ)) first last := by
  have cell_reachable : (outer.openGraph (inner.coarseConfiguration cells)).Reachable first last := by rwa [coarsens]
  have identity := substituted_distance_eq_shortest outer inner cells simple cell_reachable
  rw [substitute_distance_eq_substituted_distance outer inner cells cell_reachable]
  rw [identity, ← PathFamily.shortest_scale _ _ scalar_nonnegative]
  rw [← weightedDistance_of_reachable]
  simp only [coarsens]

/-- Convergence of the actual connected child lengths gives convergence of
every restricted skeleton distance on the same finite graph. -/
theorem actual_skeleton_distances_tendsto (outer : FiniteNetwork outerVertices outerEdges)
    (innerVertices innerEdges : ℕ → ℕ)
    (inner : ∀ depth, FiniteNetwork (innerVertices depth) (innerEdges depth))
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (cells : ∀ depth, Fin outerEdges → Configuration (innerEdges depth)) (coarse : Configuration outerEdges)
    (coarsens : ∀ depth, (inner depth).coarseConfiguration (cells depth) = coarse)
    (scalar : ℕ → ℝ) (scalar_nonnegative : ∀ depth, 0 ≤ scalar depth)
    (limit_length : Fin outerEdges → ℝ)
    (child_convergence : ∀ edge, Tendsto (fun depth => scalar depth *
      (((inner depth).openGraph (cells depth edge)).dist (inner depth).source (inner depth).target : ℝ))
        atTop (𝓝 (limit_length edge)))
    {first last : Fin outerVertices} (reachable : (outer.openGraph coarse).Reachable first last) :
    Tendsto (fun depth => scalar depth *
      (((outer.substitute (inner depth)).openGraph (substitutionConfigurationEquiv (cells depth))).dist
        (Fintype.equivFin _ (Sum.inl first)) (Fintype.equivFin _ (Sum.inl last)) : ℝ))
      atTop (𝓝 (weightedDistance (outer.openGraph coarse) (indexedBondCost outer limit_length) first last)) := by
  have bond_convergence (bond : Sym2 (Fin outerVertices)) :
      Tendsto (fun depth => scalar depth * (childDistanceCost outer (inner depth) (cells depth) bond : ℝ))
        atTop (𝓝 (indexedBondCost outer limit_length bond)) := by
    classical
    by_cases exists_edge : ∃ edge, s((outer.endpoint edge).1, (outer.endpoint edge).2) = bond
    · simp only [childDistanceCost, indexedBondCost, dif_pos exists_edge]
      exact child_convergence (Classical.choose exists_edge)
    · simp only [childDistanceCost, indexedBondCost, dif_neg exists_edge, Nat.cast_zero, mul_zero]
      exact tendsto_const_nhds
  have convergence := weightedDistance_tendsto (outer.openGraph coarse) _ _ bond_convergence first last
  apply convergence.congr'
  exact Filter.Eventually.of_forall (fun depth =>
    (actual_skeleton_restricted_distance_eq outer (inner depth) simple (cells depth) coarse
      (coarsens depth) (scalar depth) (scalar_nonnegative depth) reachable).symm)

end IGSIII.Geometry
