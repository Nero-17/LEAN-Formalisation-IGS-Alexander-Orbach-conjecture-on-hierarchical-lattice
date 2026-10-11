import Universality.Geometry.GraphRealisation
import Universality.Geometry.GraphDirectedEquation
import Universality.Geometry.FiniteTypeDiameter

namespace Universality.Geometry.GraphRealisation
noncomputable section
open Set Metric
variable {X : Type*} [MetricSpace X] (realisation : GraphRealisation X)

instance (n : ℕ) : Fintype (realisation.addresses.Node n) := realisation.addresses.finiteNode n

/-- Descendants of one first-generation cell, realised in the root space. -/
def firstChildLevel (child : realisation.addresses.Node 1) (n : ℕ) : Set X :=
  {x | ∃ w : realisation.addresses.Node (n + 1),
    realisation.addresses.project (Nat.succ_le_succ (Nat.zero_le n)) w = child ∧
    x ∈ realisation.toContractiveRealisation.cell (n + 1) w}

def intrinsicChildLevel (child : realisation.addresses.Node 1) (n : ℕ) :
    Set (realisation.Space 1 child) :=
  realisation.toContractiveRealisation.chart 1 child ⁻¹' realisation.firstChildLevel child n

theorem firstChildLevel_subset (child : realisation.addresses.Node 1) (n : ℕ) :
    realisation.firstChildLevel child n ⊆ realisation.toContractiveRealisation.cell 1 child := by
  rintro x ⟨w, hparent, hx⟩
  have h := realisation.toContractiveRealisation.cell_subset
    (Nat.succ_le_succ (Nat.zero_le n)) w hx
  rwa [hparent] at h

theorem firstChildLevel_antitone (child : realisation.addresses.Node 1) :
    Antitone (realisation.firstChildLevel child) := by
  apply antitone_nat_of_succ_le
  intro n x hx
  obtain ⟨w, hparent, hx⟩ := hx
  refine ⟨realisation.addresses.project (Nat.le_succ (n + 1)) w, ?_,
    realisation.toContractiveRealisation.cell_succ_subset (n + 1) w hx⟩
  rw [realisation.addresses.project_trans]
  exact hparent

theorem intrinsicChildLevel_antitone (child : realisation.addresses.Node 1) :
    Antitone (realisation.intrinsicChildLevel child) := by
  intro i j hij
  exact preimage_mono (realisation.firstChildLevel_antitone child hij)

theorem intrinsicChildLevel_image (child : realisation.addresses.Node 1) (n : ℕ) :
    realisation.toContractiveRealisation.chart 1 child '' realisation.intrinsicChildLevel child n =
      realisation.firstChildLevel child n := by
  exact image_preimage_eq_of_subset (realisation.firstChildLevel_subset child n)

theorem first_level_recursion (n : ℕ) :
    realisation.toCompactCellTree.level (n + 1) =
      ⋃ child : realisation.addresses.Node 1,
        realisation.toContractiveRealisation.chart 1 child '' realisation.intrinsicChildLevel child n := by
  simp_rw [realisation.intrinsicChildLevel_image]
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨realisation.addresses.project (Nat.succ_le_succ (Nat.zero_le n)) w,
      w, rfl, hw⟩
  · intro hx
    obtain ⟨child, w, _, hw⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨w, hw⟩

/-- The graph-directed recursive equation follows from the actual address
projections and contractions, rather than being supplied as an assumption. -/
theorem graphDirected_set_equation :
    realisation.toCompactCellTree.limit =
      ⋃ child : realisation.addresses.Node 1,
        realisation.toContractiveRealisation.chart 1 child ''
          (⋂ n, realisation.intrinsicChildLevel child n) := by
  exact graphDirected_limit_equation (fun child => realisation.Space 1 child)
    (realisation.toContractiveRealisation.chart 1) (realisation.chart_injective 1)
    realisation.intrinsicChildLevel realisation.intrinsicChildLevel_antitone
    realisation.toCompactCellTree.level realisation.first_level_recursion
    (realisation.toCompactCellTree.level_antitone (Nat.zero_le 1))

/-- Main pathwise geometric conclusion for a compatible contractive graph
realisation: actual persistent graph vertices, compact attractor, addresses,
and the graph-directed set recursion are all linked in the same statement. -/
theorem geometric_limit :
    realisation.toCompactCellTree.limit.Nonempty ∧
    IsCompact realisation.toCompactCellTree.limit ∧
    (∀ x : X, x ∈ realisation.toCompactCellTree.limit ↔
      ∃ address : realisation.toCompactCellTree.Address,
        ∀ n, x ∈ realisation.toCompactCellTree.cell n (address.val n)) ∧
    (∀ n, hausdorffDist (realisation.vertices n) realisation.toCompactCellTree.limit ≤
      (realisation.ratio : ℝ) ^ n * realisation.diameterBound) ∧
    realisation.toCompactCellTree.limit =
      ⋃ child : realisation.addresses.Node 1,
        realisation.toContractiveRealisation.chart 1 child ''
          (⋂ n, realisation.intrinsicChildLevel child n) :=
  ⟨realisation.toCompactCellTree.nonempty_limit, realisation.toCompactCellTree.compact_limit,
    realisation.toCompactCellTree.mem_limit_iff_address, realisation.hausdorff_vertices_le,
    realisation.graphDirected_set_equation⟩

end
end Universality.Geometry.GraphRealisation
