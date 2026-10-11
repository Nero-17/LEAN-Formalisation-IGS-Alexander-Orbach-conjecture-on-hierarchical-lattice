import IGSIII.Geometry.MarkedGromovHausdorffProkhorov

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Topology
noncomputable section
open MeasureTheory Metric Set Filter IGSIII.Geometry
open scoped _root_.Topology

/-- Uniformly vanishing full projection distortion, asymptotically dense
projection ranges, converging actual pushforward measures and exact
ordered projected marks give genuine marked GHP convergence. The same
common metric simultaneously controls spaces, measures and both marks. -/
theorem markedGHPConverges_of_uniform_projection
    (Source : ℕ → Type*) [∀ depth, MetricSpace (Source depth)]
    [∀ depth, MeasurableSpace (Source depth)] [∀ depth, BorelSpace (Source depth)]
    {Target : Type*} [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (sourceMeasure : ∀ depth, Measure (Source depth)) (targetMeasure : Measure Target)
    (sourceMark : ∀ depth, Bool → Source depth) (targetMark : Bool → Target)
    (projection : ∀ depth, Source depth → Target)
    (projectionMeasurable : ∀ depth, Measurable (projection depth))
    (distortionVanish : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ first last, |dist first last - dist (projection depth first) (projection depth last)| < tolerance)
    (projectionNet : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ point : Target, ∃ vertex : Source depth, dist point (projection depth vertex) < tolerance)
    (measureConvergence : Tendsto (fun depth =>
      levyProkhorovEDist ((sourceMeasure depth).map (projection depth)) targetMeasure) atTop (𝓝 0))
    (marks : ∀ depth side, projection depth (sourceMark depth side) = targetMark side) :
    MarkedGHPConverges Source sourceMeasure targetMeasure sourceMark targetMark := by
  intro epsilon epsilonPositive
  have measureSmall := (tendsto_order.mp measureConvergence).2
    (ENNReal.ofReal (epsilon / 4)) (by positivity)
  filter_upwards [distortionVanish (epsilon / 4) (by positivity),
    projectionNet (epsilon / 4) (by positivity), measureSmall] with depth distortion net measureSmall
  letI : Nonempty (Source depth) := ⟨sourceMark depth true⟩
  have firstNet : ∀ point : Source depth, ∃ vertex : Source depth, dist point (id vertex) ≤ 0 := by
    intro point
    exact ⟨point, by simp⟩
  have secondNet : ∀ point : Target, ∃ vertex : Source depth,
      dist point (projection depth vertex) ≤ epsilon / 4 := by
    intro point
    obtain ⟨vertex, close⟩ := net point
    exact ⟨vertex, close.le⟩
  have distortionBound : ∀ first last : Source depth,
      |dist (id first) (id last) - dist (projection depth first) (projection depth last)| ≤
        2 * (epsilon / 8) := by
    intro first last
    have bound := (distortion first last).le
    simpa only [id_eq, show 2 * (epsilon / 8) = epsilon / 4 from by ring] using bound
  have close : ∀ᵐ point ∂sourceMeasure depth, point ∉ (∅ : Set (Source depth)) →
      dist point (id (id point)) ≤ 0 := Eventually.of_forall (by intro point outside; simp)
  obtain ⟨common, firstIsometry, secondIsometry, matched, hausdorff, transport⟩ :=
    exists_common_metric_measure_of_projection id (projection depth)
      (sourceMeasure depth) ((sourceMeasure depth).map (projection depth)) targetMeasure id
      (projectionMeasurable depth) ∅ 0 (epsilon / 4) 0 (epsilon / 8)
      le_rfl (by positivity) le_rfl (by positivity) firstNet secondNet distortionBound close
  letI := common
  letI : TopologicalSpace (Source depth ⊕ Target) := common.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Source depth ⊕ Target) := borel (Source depth ⊕ Target)
  refine ⟨common, firstIsometry, secondIsometry, hausdorff.trans_lt (by linarith), ?_, ?_⟩
  · have simplified : levyProkhorovEDist ((sourceMeasure depth).map (@Sum.inl (Source depth) Target))
        (targetMeasure.map (@Sum.inr (Source depth) Target)) ≤
          ENNReal.ofReal (epsilon / 8) +
            levyProkhorovEDist ((sourceMeasure depth).map (projection depth)) targetMeasure := by
      simpa only [id_eq, zero_add, measure_empty, levyProkhorovEDist_self, add_zero] using transport
    calc
      _ ≤ _ := simplified
      _ < ENNReal.ofReal (epsilon / 4) + ENNReal.ofReal (epsilon / 4) :=
        ENNReal.add_lt_add ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < epsilon / 4)).mpr
          (by linarith)) measureSmall
      _ = ENNReal.ofReal (epsilon / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ < ENNReal.ofReal epsilon := (ENNReal.ofReal_lt_ofReal_iff epsilonPositive).mpr (by linarith)
  · intro side
    have markDistance := matched (sourceMark depth side)
    simpa only [id_eq, marks depth side] using
      markDistance.trans_lt (by linarith : epsilon / 8 < epsilon)

end
end IGSIII34.Topology
