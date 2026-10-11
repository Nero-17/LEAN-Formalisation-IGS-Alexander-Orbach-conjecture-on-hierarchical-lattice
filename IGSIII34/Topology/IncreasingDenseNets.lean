import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
namespace IGSIII34.Topology
noncomputable section
open Filter Set Metric
open scoped _root_.Topology

theorem increasing_dense_sets_eventually_net
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    (sites : ℕ → Set Space) (nested : Monotone sites)
    (dense : Dense (⋃ depth, sites depth)) (radius : ℝ) (positive : 0 < radius) :
    ∀ᶠ depth in atTop, ∀ point : Space, ∃ anchor ∈ sites depth, dist point anchor < radius := by
  classical
  obtain ⟨indices, covers⟩ := isCompact_univ.elim_finite_subcover
    (fun depth => ⋃ anchor ∈ sites depth, ball anchor radius)
    (fun _ => isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball))) (by
      intro point _
      obtain ⟨anchor, member, close⟩ := dense.exists_dist_lt point positive
      obtain ⟨depth, member⟩ := mem_iUnion.mp member
      exact mem_iUnion.mpr ⟨depth, mem_iUnion.mpr ⟨anchor, mem_iUnion.mpr ⟨member, close⟩⟩⟩)
  refine eventually_atTop.mpr ⟨indices.sup id, ?_⟩
  intro depth beyond point
  obtain ⟨index, member⟩ := mem_iUnion.mp (covers (mem_univ point))
  obtain ⟨inIndices, member⟩ := mem_iUnion.mp member
  obtain ⟨anchor, member⟩ := mem_iUnion.mp member
  obtain ⟨inSites, close⟩ := mem_iUnion.mp member
  exact ⟨anchor, nested ((Finset.le_sup (f := id) inIndices).trans beyond) inSites, close⟩

end
end IGSIII34.Topology
