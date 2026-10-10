import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.KonigLemma

/-!
# The metric limit of a finitely branching compact cell tree

This is a deterministic, pathwise theorem. Its input consists of the realised
finite-level cells, their address projections, shrinking bounds, and persistent
vertices. It does not assume that the attractor exists or that addresses code
points. Constructing this input from graph substitution is a separate step.
-/

namespace Universality.Geometry
noncomputable section
open Set Filter Metric
open scoped Topology

structure CompactCellTree (X : Type*) [MetricSpace X] where
  Node : ℕ → Type
  finiteNode : ∀ n, Fintype (Node n)
  nonemptyNode : ∀ n, Nonempty (Node n)
  project : {i j : ℕ} → i ≤ j → Node j → Node i
  project_refl : ∀ n (w : Node n), project (le_refl n) w = w
  project_trans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (w : Node k),
    project hij (project hjk w) = project (hij.trans hjk) w
  cell : (n : ℕ) → Node n → Set X
  compact_cell : ∀ n w, IsCompact (cell n w)
  nonempty_cell : ∀ n w, (cell n w).Nonempty
  cell_subset : ∀ {i j} (hij : i ≤ j) w, cell j w ⊆ cell i (project hij w)
  ratio : ℝ
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  diameterBound : ℝ
  diameterBound_nonneg : 0 ≤ diameterBound
  shrinking : ∀ n w, ∀ x ∈ cell n w, ∀ y ∈ cell n w,
    dist x y ≤ ratio ^ n * diameterBound

namespace CompactCellTree
variable {X : Type*} [MetricSpace X] (tree : CompactCellTree X)

instance (n : ℕ) : Fintype (tree.Node n) := tree.finiteNode n
instance (n : ℕ) : Nonempty (tree.Node n) := tree.nonemptyNode n

def level (n : ℕ) : Set X := ⋃ w, tree.cell n w
def limit : Set X := ⋂ n, tree.level n

theorem compact_level (n : ℕ) : IsCompact (tree.level n) :=
  isCompact_iUnion (tree.compact_cell n)

theorem nonempty_level (n : ℕ) : (tree.level n).Nonempty := by
  obtain ⟨w⟩ := tree.nonemptyNode n
  obtain ⟨x, hx⟩ := tree.nonempty_cell n w
  exact ⟨x, mem_iUnion.mpr ⟨w, hx⟩⟩

theorem level_antitone : Antitone tree.level := by
  intro i j hij x hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨tree.project hij w, tree.cell_subset hij w hw⟩

theorem nonempty_limit : tree.limit.Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed tree.level
    (fun n => tree.level_antitone (Nat.le_succ n)) tree.nonempty_level
    (tree.compact_level 0) (fun n => (tree.compact_level n).isClosed)

theorem compact_limit : IsCompact tree.limit :=
  (tree.compact_level 0).of_isClosed_subset
    (isClosed_iInter (fun n => (tree.compact_level n).isClosed))
    (iInter_subset tree.level 0)

def Address := {choice : (n : ℕ) → tree.Node n //
  ∀ {i j} (hij : i ≤ j), tree.project hij (choice j) = choice i}

theorem address_exists_of_mem_limit (x : X) (hx : x ∈ tree.limit) :
    ∃ address : tree.Address, ∀ n, x ∈ tree.cell n (address.val n) := by
  classical
  let containing (n : ℕ) := {w : tree.Node n // x ∈ tree.cell n w}
  haveI (n : ℕ) : Nonempty (containing n) := by
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hx n)
    exact ⟨⟨w, hw⟩⟩
  let project : {i j : ℕ} → i ≤ j → containing j → containing i :=
    fun hij w => ⟨tree.project hij w.val, tree.cell_subset hij w.val w.property⟩
  obtain ⟨choice, hc⟩ := exists_seq_forall_proj_of_forall_finite project
    (fun _ w => Subtype.ext (tree.project_refl _ w.val))
    (fun _ _ _ hij hjk w => Subtype.ext (tree.project_trans hij hjk w.val))
    (fun _ _ => Set.toFinite _)
  refine ⟨⟨fun n => (choice n).val, ?_⟩, fun n => (choice n).property⟩
  intro i j hij
  exact congrArg Subtype.val (hc hij)

theorem address_unique_point (address : tree.Address) :
    ∃! x : X, ∀ n, x ∈ tree.cell n (address.val n) := by
  have hnested (n : ℕ) :
      tree.cell (n + 1) (address.val (n + 1)) ⊆ tree.cell n (address.val n) := by
    have h := tree.cell_subset (Nat.le_succ n) (address.val (n + 1))
    rwa [address.property (Nat.le_succ n)] at h
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => tree.cell n (address.val n)) hnested
    (fun n => tree.nonempty_cell n _) (tree.compact_cell 0 _)
    (fun n => (tree.compact_cell n _).isClosed)
  refine ⟨x, mem_iInter.mp hx, ?_⟩
  intro y hy
  have hdist (n : ℕ) : dist y x ≤ tree.ratio ^ n * tree.diameterBound :=
    tree.shrinking n _ y (hy n) x (mem_iInter.mp hx n)
  have hzero : Tendsto (fun n : ℕ => tree.ratio ^ n * tree.diameterBound) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      tree.ratio_nonneg tree.ratio_lt_one).mul_const tree.diameterBound
  exact dist_le_zero.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hzero
    (Filter.Eventually.of_forall hdist))

theorem mem_limit_iff_address (x : X) :
    x ∈ tree.limit ↔ ∃ address : tree.Address, ∀ n, x ∈ tree.cell n (address.val n) := by
  constructor
  · exact tree.address_exists_of_mem_limit x
  · rintro ⟨address, hx⟩
    exact mem_iInter.mpr (fun n => mem_iUnion.mpr ⟨address.val n, hx n⟩)

theorem vertices_subset_limit (vertices : ℕ → Set X)
    (hpersist : Monotone vertices) (hcontained : ∀ n, vertices n ⊆ tree.level n)
    (n : ℕ) : vertices n ⊆ tree.limit := by
  intro x hx
  apply mem_iInter.mpr
  intro m
  rcases le_total n m with hnm | hmn
  · exact hcontained m (hpersist hnm hx)
  · exact tree.level_antitone hmn (hcontained n hx)

/-- A vertex in each cell suffices for the precise Hausdorff approximation
claimed in the paper. Terminal vertices supply these witnesses. -/
theorem hausdorff_vertices_le (vertices : ℕ → Set X)
    (hpersist : Monotone vertices) (hcontained : ∀ n, vertices n ⊆ tree.level n)
    (hcellVertex : ∀ n w, ∃ v ∈ vertices n, v ∈ tree.cell n w) (n : ℕ) :
    hausdorffDist (vertices n) tree.limit ≤ tree.ratio ^ n * tree.diameterBound := by
  apply hausdorffDist_le_of_mem_dist (mul_nonneg (pow_nonneg tree.ratio_nonneg n)
    tree.diameterBound_nonneg)
  · intro x hx
    exact ⟨x, tree.vertices_subset_limit vertices hpersist hcontained n hx,
      by simpa using mul_nonneg (pow_nonneg tree.ratio_nonneg n) tree.diameterBound_nonneg⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hx n)
    obtain ⟨v, hv, hvc⟩ := hcellVertex n w
    exact ⟨v, hv, tree.shrinking n w x hw v hvc⟩

theorem hausdorff_vertices_tendsto_zero (vertices : ℕ → Set X)
    (hpersist : Monotone vertices) (hcontained : ∀ n, vertices n ⊆ tree.level n)
    (hcellVertex : ∀ n w, ∃ v ∈ vertices n, v ∈ tree.cell n w) :
    Tendsto (fun n => hausdorffDist (vertices n) tree.limit) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => hausdorffDist_nonneg)
    (tree.hausdorff_vertices_le vertices hpersist hcontained hcellVertex)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    tree.ratio_nonneg tree.ratio_lt_one).mul_const tree.diameterBound

end CompactCellTree
end
end Universality.Geometry
