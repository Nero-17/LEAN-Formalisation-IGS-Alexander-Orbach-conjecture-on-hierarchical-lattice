import Universality.Geometry.CompactCellTree
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Universality.Geometry
noncomputable section
open Set Metric
open scoped NNReal

/-- The finite address sets and their prefix maps for one fixed sequence of
rule choices. Different rules and different child incidences remain distinct. -/
structure FiniteAddressTree where
  Node : ℕ → Type
  finiteNode : ∀ n, Fintype (Node n)
  nonemptyNode : ∀ n, Nonempty (Node n)
  project : {i j : ℕ} → i ≤ j → Node j → Node i
  project_refl : ∀ n (w : Node n), project (le_refl n) w = w
  project_trans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (w : Node k),
    project hij (project hjk w) = project (hij.trans hjk) w

/-- Typed cell spaces, contraction maps and their incidence in the address
tree. This data is deterministic after the rule choices have been fixed. -/
structure ContractiveRealisation (X : Type*) [MetricSpace X] where
  addresses : FiniteAddressTree
  Space : (n : ℕ) → addresses.Node n → Type
  metricSpace : ∀ n w, MetricSpace (Space n w)
  compactSpace : ∀ n w, @CompactSpace (Space n w) (metricSpace n w).toUniformSpace.toTopologicalSpace
  nonemptySpace : ∀ n w, Nonempty (Space n w)
  ratio : ℝ≥0
  ratio_lt_one : ratio < 1
  diameterBound : ℝ
  diameterBound_nonneg : 0 ≤ diameterBound
  boundedSpace : ∀ n w (x y : Space n w), @dist _ (metricSpace n w).toDist x y ≤ diameterBound
  rootMap : (w : addresses.Node 0) → Space 0 w → X
  rootLipschitz : ∀ w, @LipschitzWith _ _
    (metricSpace 0 w).toPseudoEMetricSpace inferInstance 1 (rootMap w)
  edgeMap : (n : ℕ) → (w : addresses.Node (n + 1)) →
    Space (n + 1) w → Space n (addresses.project (Nat.le_succ n) w)
  edgeLipschitz : ∀ n w, @LipschitzWith _ _
    (metricSpace (n + 1) w).toPseudoEMetricSpace
    (metricSpace n (addresses.project (Nat.le_succ n) w)).toPseudoEMetricSpace ratio (edgeMap n w)

namespace ContractiveRealisation
variable {X : Type*} [MetricSpace X] (realisation : ContractiveRealisation X)

instance (n : ℕ) (w : realisation.addresses.Node n) : MetricSpace (realisation.Space n w) :=
  realisation.metricSpace n w
instance (n : ℕ) (w : realisation.addresses.Node n) : CompactSpace (realisation.Space n w) :=
  realisation.compactSpace n w
instance (n : ℕ) (w : realisation.addresses.Node n) : Nonempty (realisation.Space n w) :=
  realisation.nonemptySpace n w

def chart (realisation : ContractiveRealisation X) :
    (n : ℕ) → (w : realisation.addresses.Node n) → realisation.Space n w → X
  | 0, w => realisation.rootMap w
  | n + 1, w => realisation.chart n (realisation.addresses.project (Nat.le_succ n) w) ∘
      realisation.edgeMap n w

theorem chart_lipschitz (n : ℕ) (w : realisation.addresses.Node n) :
    LipschitzWith (realisation.ratio ^ n) (realisation.chart n w) := by
  induction n with
  | zero => simpa only [chart, pow_zero] using realisation.rootLipschitz w
  | succ n ih =>
    simpa only [chart, pow_succ] using
      (ih (realisation.addresses.project (Nat.le_succ n) w)).comp (realisation.edgeLipschitz n w)

def cell (n : ℕ) (w : realisation.addresses.Node n) : Set X := range (realisation.chart n w)

theorem compact_cell (n : ℕ) (w : realisation.addresses.Node n) :
    IsCompact (realisation.cell n w) :=
  isCompact_range (realisation.chart_lipschitz n w).continuous

theorem nonempty_cell (n : ℕ) (w : realisation.addresses.Node n) :
    (realisation.cell n w).Nonempty := range_nonempty _

theorem cell_succ_subset (n : ℕ) (w : realisation.addresses.Node (n + 1)) :
    realisation.cell (n + 1) w ⊆
      realisation.cell n (realisation.addresses.project (Nat.le_succ n) w) := by
  rintro x ⟨y, rfl⟩
  exact ⟨realisation.edgeMap n w y, rfl⟩

theorem cell_subset {i j : ℕ} (hij : i ≤ j) (w : realisation.addresses.Node j) :
    realisation.cell j w ⊆ realisation.cell i (realisation.addresses.project hij w) := by
  induction j with
  | zero =>
    have hi : i = 0 := Nat.eq_zero_of_le_zero hij
    subst i
    rw [realisation.addresses.project_refl]
  | succ j ih =>
    by_cases heq : i = j + 1
    · subst i
      rw [realisation.addresses.project_refl]
    · have hle : i ≤ j := Nat.le_of_lt_succ (lt_of_le_of_ne hij heq)
      have h := (realisation.cell_succ_subset j w).trans
        (ih hle (realisation.addresses.project (Nat.le_succ j) w))
      rwa [realisation.addresses.project_trans] at h

theorem shrinking (n : ℕ) (w : realisation.addresses.Node n)
    (x : X) (hx : x ∈ realisation.cell n w) (y : X) (hy : y ∈ realisation.cell n w) :
    dist x y ≤ (realisation.ratio : ℝ) ^ n * realisation.diameterBound := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  simpa only [NNReal.coe_pow] using
    (realisation.chart_lipschitz n w).dist_le_mul_of_le (realisation.boundedSpace n w a b)

/-- Compactness, nesting and the geometric shrinking estimate are conclusions
of the given contractions, not assumptions about an already existing limit. -/
def toCompactCellTree : CompactCellTree X where
  Node := realisation.addresses.Node
  finiteNode := realisation.addresses.finiteNode
  nonemptyNode := realisation.addresses.nonemptyNode
  project := realisation.addresses.project
  project_refl := realisation.addresses.project_refl
  project_trans := realisation.addresses.project_trans
  cell := realisation.cell
  compact_cell := realisation.compact_cell
  nonempty_cell := realisation.nonempty_cell
  cell_subset := realisation.cell_subset
  ratio := realisation.ratio
  ratio_nonneg := realisation.ratio.coe_nonneg
  ratio_lt_one := realisation.ratio_lt_one
  diameterBound := realisation.diameterBound
  diameterBound_nonneg := realisation.diameterBound_nonneg
  shrinking := realisation.shrinking

theorem nonempty_compact_limit :
    realisation.toCompactCellTree.limit.Nonempty ∧ IsCompact realisation.toCompactCellTree.limit :=
  ⟨realisation.toCompactCellTree.nonempty_limit, realisation.toCompactCellTree.compact_limit⟩

end ContractiveRealisation
end
end Universality.Geometry
