import IGSIII.Geometry.FiniteAnchorGluing
import IGSIII.Geometry.ExceptionalTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Metric Set

theorem levyProkhorovEDist_common_embeddings_le_of_projection
    {Source Target Ambient Index : Type*}
    [MetricSpace Source] [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (firstEmbedding : Source → Ambient) (secondEmbedding : Target → Ambient)
    (firstIsometry : Isometry firstEmbedding) (secondIsometry : Isometry secondEmbedding)
    (first : Index → Source) (second : Index → Target)
    (sourceMeasure : Measure Source) (targetProjection targetMeasure : Measure Target)
    (ownership : Source → Index)
    (sourceProjectionMeasurable : Measurable (fun point => second (ownership point)))
    (bad : Set Source) (radius bridge : ℝ) (radiusNonnegative : 0 ≤ radius) (bridgeNonnegative : 0 ≤ bridge)
    (matched : ∀ index, dist (firstEmbedding (first index)) (secondEmbedding (second index)) ≤ bridge)
    (close : ∀ᵐ point ∂sourceMeasure, point ∉ bad → dist point (first (ownership point)) ≤ radius) :
    levyProkhorovEDist (sourceMeasure.map firstEmbedding) (targetMeasure.map secondEmbedding) ≤
      ENNReal.ofReal (radius + bridge) + sourceMeasure bad +
        levyProkhorovEDist (sourceMeasure.map (fun point => second (ownership point))) targetProjection +
        levyProkhorovEDist targetProjection targetMeasure := by
  have firstMeasurable := firstIsometry.continuous.measurable
  have secondMeasurable := secondIsometry.continuous.measurable
  have sourceTransport := levyProkhorovEDist_map_le_of_exceptional_set sourceMeasure
    firstEmbedding (fun point => secondEmbedding (second (ownership point)))
    firstMeasurable (secondMeasurable.comp sourceProjectionMeasurable) bad (radius + bridge)
    (add_nonneg radiusNonnegative bridgeNonnegative) (by
      filter_upwards [close] with point close
      intro outside
      have triangle := dist_triangle (firstEmbedding point) (firstEmbedding (first (ownership point)))
        (secondEmbedding (second (ownership point)))
      rw [firstIsometry.dist_eq] at triangle
      exact triangle.trans (add_le_add (close outside) (matched _)))
  have projectedTransport := levyProkhorovEDist_map_le_of_lipschitz_one
    (sourceMeasure.map (fun point => second (ownership point))) targetProjection secondEmbedding secondIsometry.lipschitz
  rw [Measure.map_map secondMeasurable sourceProjectionMeasurable] at projectedTransport
  have targetTransport := levyProkhorovEDist_map_le_of_lipschitz_one
    targetProjection targetMeasure secondEmbedding secondIsometry.lipschitz
  exact (levyProkhorovEDist_triangle _ _ _).trans
    (add_le_add sourceTransport ((levyProkhorovEDist_triangle _ _ _).trans
      (add_le_add projectedTransport targetTransport))) |>.trans_eq (by ac_rfl)

theorem exists_common_metric_measure_of_projection
    {Source Target Index : Type*}
    [MetricSpace Source] [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target] [Nonempty Index]
    (first : Index → Source) (second : Index → Target)
    (sourceMeasure : Measure Source) (targetProjection targetMeasure : Measure Target)
    (ownership : Source → Index)
    (sourceProjectionMeasurable : Measurable (fun point => second (ownership point)))
    (bad : Set Source) (first_mesh second_mesh radius bridge : ℝ)
    (first_nonnegative : 0 ≤ first_mesh) (second_nonnegative : 0 ≤ second_mesh)
    (radiusNonnegative : 0 ≤ radius) (bridgePositive : 0 < bridge)
    (first_net : ∀ point : Source, ∃ index, dist point (first index) ≤ first_mesh)
    (second_net : ∀ point : Target, ∃ index, dist point (second index) ≤ second_mesh)
    (distortion : ∀ left right, |dist (first left) (first right) - dist (second left) (second right)| ≤ 2 * bridge)
    (close : ∀ᵐ point ∂sourceMeasure, point ∉ bad → dist point (first (ownership point)) ≤ radius) :
    ∃ common : MetricSpace (Source ⊕ Target),
      letI := common
      letI : TopologicalSpace (Source ⊕ Target) := common.toUniformSpace.toTopologicalSpace
      letI : MeasurableSpace (Source ⊕ Target) := borel (Source ⊕ Target)
      Isometry (@Sum.inl Source Target) ∧ Isometry (@Sum.inr Source Target) ∧
      (∀ index, dist (Sum.inl (first index)) (Sum.inr (second index)) = bridge) ∧
      hausdorffDist (Set.range (@Sum.inl Source Target)) (Set.range (@Sum.inr Source Target)) ≤
        first_mesh + bridge + second_mesh ∧
      levyProkhorovEDist (sourceMeasure.map (@Sum.inl Source Target)) (targetMeasure.map (@Sum.inr Source Target)) ≤
        ENNReal.ofReal (radius + bridge) + sourceMeasure bad +
          levyProkhorovEDist (sourceMeasure.map (fun point => second (ownership point))) targetProjection +
          levyProkhorovEDist targetProjection targetMeasure := by
  obtain ⟨common, firstIsometry, secondIsometry, matched, hausdorff⟩ :=
    exists_common_metric_of_anchor_distortion first second first_mesh second_mesh bridge
      first_nonnegative second_nonnegative bridgePositive first_net second_net distortion
  letI := common
  letI : TopologicalSpace (Source ⊕ Target) := common.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Source ⊕ Target) := borel (Source ⊕ Target)
  letI : BorelSpace (Source ⊕ Target) := ⟨rfl⟩
  exact ⟨common, firstIsometry, secondIsometry, matched, hausdorff,
    levyProkhorovEDist_common_embeddings_le_of_projection _ _ firstIsometry secondIsometry
      first second sourceMeasure targetProjection targetMeasure ownership sourceProjectionMeasurable
      bad radius bridge radiusNonnegative bridgePositive.le (fun index => (matched index).le) close⟩

/-- The common metric made from finite anchors simultaneously controls the
whole spaces, their actual measures, and every mark among the anchors. -/
theorem exists_common_metric_measure_of_anchor_distortion
    {Source Target Index Sample : Type*}
    [MetricSpace Source] [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    [Nonempty Index] [MeasurableSpace Sample]
    (first : Index → Source) (second : Index → Target)
    (sourceMeasure : Measure Source) (sampleMeasure : Measure Sample)
    (ownership : Source → Index) (representative : Sample → Index) (realization : Sample → Target)
    (sourceProjectionMeasurable : Measurable (fun point => second (ownership point)))
    (sampleProjectionMeasurable : Measurable (fun sample => second (representative sample)))
    (realizationMeasurable : Measurable realization)
    (bad : Set Source) (first_mesh second_mesh source_radius target_radius bridge : ℝ)
    (first_nonnegative : 0 ≤ first_mesh) (second_nonnegative : 0 ≤ second_mesh)
    (source_nonnegative : 0 ≤ source_radius) (target_nonnegative : 0 ≤ target_radius)
    (bridge_positive : 0 < bridge)
    (first_net : ∀ point : Source, ∃ index, dist point (first index) ≤ first_mesh)
    (second_net : ∀ point : Target, ∃ index, dist point (second index) ≤ second_mesh)
    (distortion : ∀ left right, |dist (first left) (first right) - dist (second left) (second right)| ≤ 2 * bridge)
    (source_close : ∀ᵐ point ∂sourceMeasure, point ∉ bad → dist point (first (ownership point)) ≤ source_radius)
    (target_close : ∀ᵐ sample ∂sampleMeasure, dist (second (representative sample)) (realization sample) ≤ target_radius) :
    ∃ common : MetricSpace (Source ⊕ Target),
      letI := common
      letI : TopologicalSpace (Source ⊕ Target) := common.toUniformSpace.toTopologicalSpace
      letI : MeasurableSpace (Source ⊕ Target) := borel (Source ⊕ Target)
      Isometry (@Sum.inl Source Target) ∧ Isometry (@Sum.inr Source Target) ∧
      (∀ index, dist (Sum.inl (first index)) (Sum.inr (second index)) = bridge) ∧
      hausdorffDist (Set.range (@Sum.inl Source Target)) (Set.range (@Sum.inr Source Target)) ≤
        first_mesh + bridge + second_mesh ∧
      levyProkhorovEDist (sourceMeasure.map (@Sum.inl Source Target))
        ((sampleMeasure.map realization).map (@Sum.inr Source Target)) ≤
          ENNReal.ofReal (source_radius + bridge) + sourceMeasure bad +
            levyProkhorovEDist (sourceMeasure.map (fun point => second (ownership point)))
              (sampleMeasure.map (fun sample => second (representative sample))) +
            ENNReal.ofReal target_radius := by
  obtain ⟨common, firstIsometry, secondIsometry, matched, hausdorff⟩ :=
    exists_common_metric_of_anchor_distortion first second first_mesh second_mesh bridge
      first_nonnegative second_nonnegative bridge_positive first_net second_net distortion
  letI := common
  letI : TopologicalSpace (Source ⊕ Target) := common.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Source ⊕ Target) := borel (Source ⊕ Target)
  letI : BorelSpace (Source ⊕ Target) := ⟨rfl⟩
  have firstMeasurable := firstIsometry.continuous.measurable
  have secondMeasurable := secondIsometry.continuous.measurable
  have firstTransport := levyProkhorovEDist_map_le_of_exceptional_set sourceMeasure
    (@Sum.inl Source Target) (fun point => Sum.inr (second (ownership point)))
    firstMeasurable (secondMeasurable.comp sourceProjectionMeasurable) bad (source_radius + bridge)
    (by linarith) (by
      filter_upwards [source_close] with point close
      intro outside
      have triangle := dist_triangle (Sum.inl point) (Sum.inl (first (ownership point)))
        (Sum.inr (second (ownership point)))
      rw [firstIsometry.dist_eq, matched] at triangle
      exact triangle.trans (add_le_add (close outside) le_rfl))
  have secondTransport := levyProkhorovEDist_map_le_of_lipschitz_one
    (sourceMeasure.map (fun point => second (ownership point)))
    (sampleMeasure.map (fun sample => second (representative sample)))
    (@Sum.inr Source Target) secondIsometry.lipschitz
  rw [Measure.map_map secondMeasurable sourceProjectionMeasurable,
    Measure.map_map secondMeasurable sampleProjectionMeasurable] at secondTransport
  have targetTransport := levyProkhorovEDist_map_le_of_exceptional_set sampleMeasure
    (fun sample => Sum.inr (second (representative sample))) (fun sample => Sum.inr (realization sample))
    (secondMeasurable.comp sampleProjectionMeasurable) (secondMeasurable.comp realizationMeasurable)
    ∅ target_radius target_nonnegative (by
      filter_upwards [target_close] with sample close
      intro _
      simpa only [secondIsometry.dist_eq] using close)
  simp only [measure_empty, add_zero] at targetTransport
  refine ⟨common, firstIsometry, secondIsometry, matched, hausdorff, ?_⟩
  rw [Measure.map_map secondMeasurable realizationMeasurable]
  exact (levyProkhorovEDist_triangle _ _ _).trans
    (add_le_add firstTransport ((levyProkhorovEDist_triangle _ _ _).trans
      (add_le_add secondTransport targetTransport))) |>.trans_eq (by ac_rfl)

end
end IGSIII.Geometry
