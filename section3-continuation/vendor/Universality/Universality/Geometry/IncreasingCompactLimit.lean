import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Universality.Geometry
noncomputable section
open Set Metric Filter
open scoped Topology

/-- Increasing sets approximate the compact closure of their union uniformly. -/
theorem increasing_sets_hausdorff_bound {X : Type*} [MetricSpace X]
    (vertices : ℕ → Set X) (hincreasing : Monotone vertices)
    (hnonempty : ∀ n, (vertices n).Nonempty)
    (hcompact : IsCompact (closure (⋃ n, vertices n)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ depth, ∀ n ≥ depth,
      hausdorffDist (vertices n) (closure (⋃ k, vertices k)) ≤ epsilon := by
  classical
  have hcover : closure (⋃ n, vertices n) ⊆
      ⋃ n, ⋃ point ∈ vertices n, ball point epsilon := by
    intro point hpoint
    obtain ⟨nearby, hnearby, hdist⟩ := Metric.mem_closure_iff.mp hpoint epsilon hepsilon
    obtain ⟨n, hn⟩ := mem_iUnion.mp hnearby
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨nearby, mem_iUnion.mpr ⟨hn,
      by simpa only [mem_ball, dist_comm] using hdist⟩⟩⟩
  obtain ⟨levels, hlevels⟩ := hcompact.elim_finite_subcover
    (fun n => ⋃ point ∈ vertices n, ball point epsilon)
    (fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball) hcover
  refine ⟨levels.sup id, fun n hn => hausdorffDist_le_of_mem_dist hepsilon.le ?_ ?_⟩
  · intro point hpoint
    exact ⟨point, subset_closure (mem_iUnion.mpr ⟨n, hpoint⟩), by simp [hepsilon.le]⟩
  · intro point hpoint
    obtain ⟨level, hlevel⟩ := mem_iUnion.mp (hlevels hpoint)
    obtain ⟨hmember, hmemberPoint⟩ := mem_iUnion.mp hlevel
    obtain ⟨nearby, hnearby⟩ := mem_iUnion.mp hmemberPoint
    obtain ⟨hnearby, hdist⟩ := mem_iUnion.mp hnearby
    exact ⟨nearby, hincreasing ((Finset.le_sup (f := id) hmember).trans hn) hnearby,
      (by simpa only [mem_ball, dist_comm] using hdist.le)⟩

theorem increasing_sets_hausdorff_tendsto {X : Type*} [MetricSpace X]
    (vertices : ℕ → Set X) (hincreasing : Monotone vertices)
    (hnonempty : ∀ n, (vertices n).Nonempty)
    (hcompact : IsCompact (closure (⋃ n, vertices n))) :
    Tendsto (fun n => hausdorffDist (vertices n) (closure (⋃ k, vertices k))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨depth, hdepth⟩ := increasing_sets_hausdorff_bound vertices hincreasing hnonempty
    hcompact (epsilon / 2) (half_pos hepsilon)
  refine ⟨depth, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  exact (hdepth n hn).trans_lt (half_lt_self hepsilon)

end
end Universality.Geometry
