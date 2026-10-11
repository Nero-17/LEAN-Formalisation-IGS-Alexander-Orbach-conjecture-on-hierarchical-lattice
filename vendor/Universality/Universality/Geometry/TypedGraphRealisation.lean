import Universality.Geometry.GraphDirectedLimit
import Universality.Geometry.RuleFamilies
import Mathlib.Topology.MetricSpace.Isometry

namespace Universality.Geometry
noncomputable section
open Set Metric

/-- A compatible realisation carries the original finite colours and rule
laws. Cell spaces are copies of the fixed compact space of their colour. -/
structure TypedGraphRealisation {Colour : Type*} [Fintype Colour]
    (Space : Colour → Type*) [∀ i, MetricSpace (Space i)]
    (families : RuleFamilies Colour) (X : Type*) [MetricSpace X] where
  graph : GraphRealisation X
  colour : ∀ n, graph.addresses.Node n → Colour
  choice : ∀ n w, families.Choice (colour n w)
  selected_rule : ∀ n w, graph.rule n w = families.rule (colour n w) (choice n w)
  child_colour : ∀ n w (e : Fin (graph.rule n w).edges),
    colour (n + 1) (graph.children n ⟨w, e⟩) =
      families.childColour (colour n w) (choice n w)
        (Fin.cast (congrArg Rule.edges (selected_rule n w)) e)
  cellType : ∀ n w, @IsometryEquiv (graph.Space n w) (Space (colour n w))
    (graph.metricSpace n w).toPseudoEMetricSpace inferInstance

namespace TypedGraphRealisation
variable {Colour : Type*} [Fintype Colour] [Nonempty Colour]
variable {Space : Colour → Type*} [∀ i, MetricSpace (Space i)] [∀ i, CompactSpace (Space i)]
variable {families : RuleFamilies Colour} {X : Type*} [MetricSpace X]
variable (realisation : TypedGraphRealisation Space families X)

/-- The construction-graph edge retains the rule choice and the actual
edge incidence. Its endpoint type is the inherited child colour. -/
def directedEdge (n : ℕ) (w : realisation.graph.addresses.Node n)
    (e : Fin (realisation.graph.rule n w).edges) :
    families.Transition (realisation.colour n w)
      (realisation.colour (n + 1) (realisation.graph.children n ⟨w, e⟩)) :=
  ⟨realisation.choice n w,
    Fin.cast (congrArg Rule.edges (realisation.selected_rule n w)) e,
    (realisation.child_colour n w e).symm⟩

omit [Nonempty Colour] [∀ i, CompactSpace (Space i)] in
theorem directedEdge_rule (n : ℕ) (w : realisation.graph.addresses.Node n)
    (e : Fin (realisation.graph.rule n w).edges) :
    (realisation.directedEdge n w e).1 = realisation.choice n w := rfl

theorem shrinking_with_maximum (n : ℕ) (w : realisation.graph.addresses.Node n)
    (x : X) (hx : x ∈ realisation.graph.toContractiveRealisation.cell n w)
    (y : X) (hy : y ∈ realisation.graph.toContractiveRealisation.cell n w) :
    dist x y ≤ (realisation.graph.ratio : ℝ) ^ n * maximumTypeDiameter Space := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hbound : dist a b ≤ maximumTypeDiameter Space := by
    rw [← (realisation.cellType n w).dist_eq a b]
    exact type_dist_le_maximum Space _ _ _
  simpa only [NNReal.coe_pow] using
    (realisation.graph.toContractiveRealisation.chart_lipschitz n w).dist_le_mul_of_le hbound

/-- The exact finite-colour Hausdorff bound, using max_i diam(X_i), rather
than a separately assumed uniform bound. -/
theorem hausdorff_vertices_le_maximum (n : ℕ) :
    hausdorffDist (realisation.graph.vertices n) realisation.graph.toCompactCellTree.limit ≤
      (realisation.graph.ratio : ℝ) ^ n * maximumTypeDiameter Space := by
  have hnonneg : 0 ≤ (realisation.graph.ratio : ℝ) ^ n * maximumTypeDiameter Space :=
    mul_nonneg (pow_nonneg realisation.graph.ratio.coe_nonneg n) (maximumTypeDiameter_nonneg Space)
  apply hausdorffDist_le_of_mem_dist hnonneg
  · intro x hx
    exact ⟨x, realisation.graph.toCompactCellTree.vertices_subset_limit realisation.graph.vertices
      realisation.graph.vertices_monotone realisation.graph.vertices_subset_level n hx,
      by simpa using hnonneg⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hx n)
    obtain ⟨v, hv, hvc⟩ := realisation.graph.terminal_in_each_cell n w
    exact ⟨v, hv, realisation.shrinking_with_maximum n w x hw v hvc⟩

/-- Pathwise form of thm:eigs-graph-directed. It applies to every fixed
realisation of the whole-rule selections. Both descriptions use the same
retained colours, selected rules, edge incidences, maps and rule laws. -/
theorem geometric_limit :
    realisation.graph.toCompactCellTree.limit.Nonempty ∧
    IsCompact realisation.graph.toCompactCellTree.limit ∧
    (∀ address : realisation.graph.toCompactCellTree.Address,
      ∃! x : X, ∀ n, x ∈ realisation.graph.toCompactCellTree.cell n (address.val n)) ∧
    (∀ x : X, x ∈ realisation.graph.toCompactCellTree.limit ↔
      ∃ address : realisation.graph.toCompactCellTree.Address,
        ∀ n, x ∈ realisation.graph.toCompactCellTree.cell n (address.val n)) ∧
    (∀ n, hausdorffDist (realisation.graph.vertices n) realisation.graph.toCompactCellTree.limit ≤
      (realisation.graph.ratio : ℝ) ^ n * maximumTypeDiameter Space) ∧
    realisation.graph.toCompactCellTree.limit =
      ⋃ child : realisation.graph.addresses.Node 1,
        realisation.graph.toContractiveRealisation.chart 1 child ''
          (⋂ n, realisation.graph.intrinsicChildLevel child n) :=
  ⟨realisation.graph.toCompactCellTree.nonempty_limit,
    realisation.graph.toCompactCellTree.compact_limit,
    realisation.graph.toCompactCellTree.address_unique_point,
    realisation.graph.toCompactCellTree.mem_limit_iff_address,
    realisation.hausdorff_vertices_le_maximum, realisation.graph.graphDirected_set_equation⟩

end TypedGraphRealisation
end
end Universality.Geometry
