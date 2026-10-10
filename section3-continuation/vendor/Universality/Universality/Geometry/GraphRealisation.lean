import Universality.Geometry.ContractiveRealisation
import Universality.Graph.Rule

namespace Universality.Geometry
noncomputable section
open Set Metric
open scoped Topology

/-- Compatible finite rule incidence in a contractive cell realisation.
The index equivalence retains every selected rule edge separately. Endpoint
identities are written in the ambient space to avoid arbitrary transports
between the dependent cell-space types. -/
structure GraphRealisation (X : Type*) [MetricSpace X] extends ContractiveRealisation X where
  rootMap_injective : ∀ w, Function.Injective (rootMap w)
  source : ∀ n w, Space n w
  target : ∀ n w, Space n w
  terminals_distinct : ∀ n w, source n w ≠ target n w
  rule : ∀ n, addresses.Node n → Rule
  placement : ∀ n w, Fin (rule n w).vertices → Space n w
  placement_injective : ∀ n w, Function.Injective (placement n w)
  planting_source : ∀ n w, placement n w (rule n w).network.source = source n w
  planting_target : ∀ n w, placement n w (rule n w).network.target = target n w
  no_isolated : ∀ n w v, ∃ e : Fin (rule n w).edges,
    ((rule n w).network.endpoint e).1 = v ∨ ((rule n w).network.endpoint e).2 = v
  children : ∀ n, ((w : addresses.Node n) × Fin (rule n w).edges) ≃ addresses.Node (n + 1)
  child_parent : ∀ n w e, addresses.project (Nat.le_succ n) (children n ⟨w, e⟩) = w
  endpoint_source : ∀ n w e,
    toContractiveRealisation.chart (n + 1) (children n ⟨w, e⟩)
      (source (n + 1) (children n ⟨w, e⟩)) =
    toContractiveRealisation.chart n w (placement n w ((rule n w).network.endpoint e).1)
  endpoint_target : ∀ n w e,
    toContractiveRealisation.chart (n + 1) (children n ⟨w, e⟩)
      (target (n + 1) (children n ⟨w, e⟩)) =
    toContractiveRealisation.chart n w (placement n w ((rule n w).network.endpoint e).2)
  edgeMap_injective : ∀ n w, Function.Injective (edgeMap n w)
  child_intersection : ∀ n w (e f : Fin (rule n w).edges), e ≠ f →
    toContractiveRealisation.cell (n + 1) (children n ⟨w, e⟩) ∩
      toContractiveRealisation.cell (n + 1) (children n ⟨w, f⟩) =
    (toContractiveRealisation.chart n w ∘ placement n w) ''
      ({((rule n w).network.endpoint e).1, ((rule n w).network.endpoint e).2} ∩
       {((rule n w).network.endpoint f).1, ((rule n w).network.endpoint f).2})

namespace GraphRealisation
variable {X : Type*} [MetricSpace X] (realisation : GraphRealisation X)

theorem chart_injective (n : ℕ) (w : realisation.addresses.Node n) :
    Function.Injective (realisation.toContractiveRealisation.chart n w) := by
  induction n with
  | zero => exact realisation.rootMap_injective w
  | succ n ih => exact (ih _).comp (realisation.edgeMap_injective n w)

def vertices (n : ℕ) : Set X := {x | ∃ w : realisation.addresses.Node n,
  x = realisation.toContractiveRealisation.chart n w (realisation.source n w) ∨
  x = realisation.toContractiveRealisation.chart n w (realisation.target n w)}

theorem placed_vertex_mem_next (n : ℕ) (w : realisation.addresses.Node n)
    (v : Fin (realisation.rule n w).vertices) :
    realisation.toContractiveRealisation.chart n w (realisation.placement n w v) ∈
      realisation.vertices (n + 1) := by
  obtain ⟨e, he | he⟩ := realisation.no_isolated n w v
  · exact ⟨realisation.children n ⟨w, e⟩,
      Or.inl (by rw [realisation.endpoint_source, he])⟩
  · exact ⟨realisation.children n ⟨w, e⟩,
      Or.inr (by rw [realisation.endpoint_target, he])⟩

theorem vertices_succ_eq_rule_vertices (n : ℕ) :
    realisation.vertices (n + 1) = ⋃ w,
      range (realisation.toContractiveRealisation.chart n w ∘ realisation.placement n w) := by
  ext x
  constructor
  · rintro ⟨child, hx | hx⟩
    · obtain ⟨⟨w, e⟩, rfl⟩ := (realisation.children n).surjective child
      exact mem_iUnion.mpr ⟨w, ⟨((realisation.rule n w).network.endpoint e).1,
        (realisation.endpoint_source n w e).symm.trans hx.symm⟩⟩
    · obtain ⟨⟨w, e⟩, rfl⟩ := (realisation.children n).surjective child
      exact mem_iUnion.mpr ⟨w, ⟨((realisation.rule n w).network.endpoint e).2,
        (realisation.endpoint_target n w e).symm.trans hx.symm⟩⟩
  · intro hx
    obtain ⟨w, v, rfl⟩ := mem_iUnion.mp hx
    exact realisation.placed_vertex_mem_next n w v

theorem vertices_monotone : Monotone realisation.vertices := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨w, rfl | rfl⟩ := hx
  · simpa only [realisation.planting_source] using
      realisation.placed_vertex_mem_next n w (realisation.rule n w).network.source
  · simpa only [realisation.planting_target] using
      realisation.placed_vertex_mem_next n w (realisation.rule n w).network.target

theorem vertices_subset_level (n : ℕ) :
    realisation.vertices n ⊆ realisation.toCompactCellTree.level n := by
  rintro x ⟨w, rfl | rfl⟩
  · exact mem_iUnion.mpr ⟨w, ⟨realisation.source n w, rfl⟩⟩
  · exact mem_iUnion.mpr ⟨w, ⟨realisation.target n w, rfl⟩⟩

theorem terminal_in_each_cell (n : ℕ) (w : realisation.addresses.Node n) :
    ∃ v ∈ realisation.vertices n, v ∈ realisation.toCompactCellTree.cell n w :=
  ⟨realisation.toContractiveRealisation.chart n w (realisation.source n w),
    ⟨w, Or.inl rfl⟩, ⟨realisation.source n w, rfl⟩⟩

/-- The realised substitution vertices converge to the nonempty compact
address limit with exactly the estimate in thm:eigs-graph-directed. -/
theorem hausdorff_vertices_le (n : ℕ) :
    hausdorffDist (realisation.vertices n) realisation.toCompactCellTree.limit ≤
      (realisation.ratio : ℝ) ^ n * realisation.diameterBound :=
  realisation.toCompactCellTree.hausdorff_vertices_le realisation.vertices
    realisation.vertices_monotone realisation.vertices_subset_level realisation.terminal_in_each_cell n

theorem hausdorff_vertices_tendsto_zero :
    Filter.Tendsto (fun n => hausdorffDist (realisation.vertices n)
      realisation.toCompactCellTree.limit) Filter.atTop (𝓝 0) :=
  realisation.toCompactCellTree.hausdorff_vertices_tendsto_zero realisation.vertices
    realisation.vertices_monotone realisation.vertices_subset_level realisation.terminal_in_each_cell

end GraphRealisation
end
end Universality.Geometry
