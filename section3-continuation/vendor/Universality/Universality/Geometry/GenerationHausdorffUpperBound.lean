import Universality.Geometry.GenerationCompactness
import Universality.Percolation.UniformGenerationVolume
import Universality.Geometry.GeometricCovers
import Universality.Geometry.FiniteCoverHausdorffBound

namespace Universality.Rule
noncomputable section
open Set Metric

/-- Every metric realisation of the actual rescaled generation distances
with dense persistent vertices has the genuine metric Hausdorff upper bound.
The metric hypotheses are constructed for classical rules in
`exists_compact_generation_metric`; no dimension identification is assumed. -/
theorem Classical.dimH_le_of_generation_realisation {rule : Rule} (h : rule.Classical)
    {Ambient : Type*} [MetricSpace Ambient]
    (inclusion : (depth : ℕ) → Fin (rule.generation depth).vertices → Ambient)
    (hdistance : ∀ depth first second,
      dist (inclusion depth first) (inclusion depth second) = scaledGenerationDistance rule depth first second)
    (hcompatible : ∀ depth vertex, inclusion depth vertex =
      inclusion (depth + 1) (rule.generationOldVertex depth vertex))
    (hdense : Dense (⋃ depth, Set.range (inclusion depth))) :
    dimH (Set.univ : Set Ambient) ≤ ENNReal.ofReal
      (Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  letI : MeasurableSpace Ambient := borel Ambient
  letI : BorelSpace Ambient := ⟨rfl⟩
  let radius := Finset.univ.sup (fun vertex =>
    rule.network.fullGraph.dist rule.network.source vertex)
  have hradius (vertex) : rule.network.fullGraph.dist rule.network.source vertex ≤ radius :=
    Finset.le_sup (Finset.mem_univ vertex)
  let ratio : ℝ := (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)⁻¹
  let constant : ℝ := (radius : ℝ) /
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ 2
  have hratio : 0 < ratio := inv_pos.mpr h.scale_real_pos
  have hratioOne : ratio < 1 :=
    (inv_lt_one₀ h.scale_real_pos).mpr (by exact_mod_cast h.scale)
  have hconstant : 0 ≤ constant := by dsimp [constant]; positivity
  have hnested : Monotone (fun depth => Set.range (inclusion depth)) := by
    apply monotone_nat_of_le_succ
    intro depth point hpoint
    obtain ⟨vertex, rfl⟩ := hpoint
    exact ⟨rule.generationOldVertex depth vertex, (hcompatible depth vertex).symm⟩
  have hstep (depth) (point : Fin (rule.generation (depth + 1)).vertices) :
      ∃ previous : Fin (rule.generation depth).vertices,
        dist (inclusion (depth + 1) point) (inclusion depth previous) ≤ constant * ratio ^ depth := by
    obtain ⟨previous, hprevious⟩ := h.generation_vertex_near_old radius hradius depth point
    refine ⟨previous, ?_⟩
    calc
      dist (inclusion (depth + 1) point) (inclusion depth previous) =
          scaledGenerationDistance rule (depth + 1) (rule.generationOldVertex depth previous) point := by
            rw [hcompatible depth previous, dist_comm, hdistance]
      _ ≤ (radius : ℝ) /
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 2) := hprevious
      _ = constant * ratio ^ depth := by
        simp [constant, ratio, pow_add, div_eq_mul_inv, mul_comm, mul_left_comm]
  let cover (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) : Set Ambient :=
    Metric.closedBall (inclusion depth vertex) (constant / (1 - ratio) * ratio ^ depth)
  have hcover (depth) : (Set.univ : Set Ambient) ⊆ ⋃ vertex, cover depth vertex := by
    have hbound := Geometry.closure_union_subset_level_closedBalls_of_geometric_steps
      (fun depth => Fin (rule.generation depth).vertices) inclusion hnested constant ratio
      hconstant hratio.le hratioOne hstep depth
    simpa only [hdense.closure_eq] using hbound
  have hdiameter (depth) (vertex : Fin (rule.generation depth).vertices)
      (first : Ambient) (hfirst : first ∈ cover depth vertex)
      (second : Ambient) (hsecond : second ∈ cover depth vertex) :
      dist first second ≤ ratio ^ depth * (2 * (constant / (1 - ratio))) := by
    change dist first (inclusion depth vertex) ≤ constant / (1 - ratio) * ratio ^ depth at hfirst
    change dist second (inclusion depth vertex) ≤ constant / (1 - ratio) * ratio ^ depth at hsecond
    calc
      dist first second ≤ dist first (inclusion depth vertex) +
          dist (inclusion depth vertex) second := dist_triangle _ _ _
      _ ≤ constant / (1 - ratio) * ratio ^ depth + constant / (1 - ratio) * ratio ^ depth :=
        add_le_add hfirst (by simpa only [dist_comm] using hsecond)
      _ = _ := by ring
  obtain ⟨countConstant, hcountConstant, hcount⟩ := h.generation_volume_uniform_bound
  have hbound := Geometry.dimH_le_of_finite_geometric_cover
    (fun depth => Fin (rule.generation depth).vertices) Set.univ cover
    ratio (2 * (constant / (1 - ratio))) countConstant hratio hratioOne
    hcountConstant.le rule.edges (lt_trans Nat.zero_lt_one h.edges_gt_one)
    (fun depth => by simpa only [Fintype.card_fin] using hcount depth) hdiameter hcover
  simpa only [ratio, Real.log_inv, neg_neg] using hbound

/-- A classical rule has a compact complete realisation of its actual
rescaled generation metrics whose Hausdorff dimension has the claimed upper
bound. This does not assert the matching lower bound. -/
theorem Classical.exists_compact_generation_metric_with_dimH_bound {rule : Rule} (h : rule.Classical) :
    ∃ (Ambient : Type) (metric : MetricSpace Ambient),
      letI := metric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ inclusion : (depth : ℕ) → Fin (rule.generation depth).vertices → Ambient,
        (∀ depth first second,
          dist (inclusion depth first) (inclusion depth second) =
            scaledGenerationDistance rule depth first second) ∧
        (∀ depth vertex, inclusion depth vertex =
          inclusion (depth + 1) (rule.generationOldVertex depth vertex)) ∧
        Dense (⋃ depth, Set.range (inclusion depth)) ∧
        dimH (Set.univ : Set Ambient) ≤ ENNReal.ofReal
          (Real.log (rule.edges : ℝ) /
            Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  obtain ⟨Ambient, metric, hcomplete, hcompact, inclusion, hdistance, hcompatible, hdense⟩ :=
    h.exists_compact_generation_metric
  letI := metric
  exact ⟨Ambient, metric, hcomplete, hcompact, inclusion, hdistance, hcompatible, hdense,
    h.dimH_le_of_generation_realisation inclusion hdistance hcompatible hdense⟩

end
end Universality.Rule

