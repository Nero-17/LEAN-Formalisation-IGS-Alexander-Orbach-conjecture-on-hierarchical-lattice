import IGSIII.Geometry.FiniteAnchorMeasuredGluing

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

/-- Marked GHP convergence expressed by genuine common metric embeddings,
with the same common metric controlling space, measure, and ordered marks. -/
def MarkedGHPConverges
    (Source : ℕ → Type*) [∀ depth, MetricSpace (Source depth)] [∀ depth, MeasurableSpace (Source depth)]
    {Target : Type*} [MetricSpace Target] [MeasurableSpace Target]
    (sourceMeasure : ∀ depth, Measure (Source depth)) (targetMeasure : Measure Target)
    (sourceMark : ∀ depth, Bool → Source depth) (targetMark : Bool → Target) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ depth in atTop,
    ∃ common : MetricSpace (Source depth ⊕ Target),
      letI := common
      letI : TopologicalSpace (Source depth ⊕ Target) := common.toUniformSpace.toTopologicalSpace
      letI : MeasurableSpace (Source depth ⊕ Target) := borel (Source depth ⊕ Target)
      Isometry (@Sum.inl (Source depth) Target) ∧ Isometry (@Sum.inr (Source depth) Target) ∧
      hausdorffDist (range (@Sum.inl (Source depth) Target)) (range (@Sum.inr (Source depth) Target)) < epsilon ∧
      levyProkhorovEDist ((sourceMeasure depth).map (@Sum.inl (Source depth) Target))
        (targetMeasure.map (@Sum.inr (Source depth) Target)) < ENNReal.ofReal epsilon ∧
      ∀ side, dist (Sum.inl (sourceMark depth side)) (Sum.inr (targetMark side)) < epsilon

theorem markedGHPConverges_of_finite_anchor_projections
    (Source : ℕ → Type*) [∀ depth, MetricSpace (Source depth)] [∀ depth, MeasurableSpace (Source depth)]
    [∀ depth, BorelSpace (Source depth)]
    {Target : Type*} [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (Index : ℕ → Type*) [∀ age, Nonempty (Index age)]
    (sourceMeasure : ∀ depth, Measure (Source depth)) (targetMeasure : Measure Target)
    (sourceMark : ∀ depth, Bool → Source depth) (targetMark : Bool → Target)
    (first : ∀ age fine, Index age → Source (fine + (age + 1))) (second : ∀ age, Index age → Target)
    (ownership : ∀ age fine, Source (fine + (age + 1)) → Index age)
    (projectionMeasurable : ∀ age depth, Measurable (fun point => second age (ownership age depth point)))
    (bad : ∀ age fine, Set (Source (fine + (age + 1)))) (projection : ℕ → Measure Target)
    (mesh : ℕ → ℝ) (meshNonnegative : ∀ age, 0 ≤ mesh age)
    (meshConvergence : Tendsto mesh atTop (𝓝 0)) (start : ℕ)
    (firstNet : ∀ age, start ≤ age → ∀ᶠ depth in atTop,
      ∀ point : Source (depth + (age + 1)), ∃ index, dist point (first age depth index) ≤ mesh age)
    (secondNet : ∀ age, start ≤ age → ∀ point : Target, ∃ index, dist point (second age index) ≤ mesh age)
    (distortion : ∀ age (bridge : ℝ), 0 < bridge → ∀ᶠ depth in atTop,
      ∀ left right : Index age, |dist (first age depth left) (first age depth right) -
        dist (second age left) (second age right)| ≤ 2 * bridge)
    (close : ∀ age, start ≤ age → ∀ᶠ depth in atTop,
      ∀ᵐ point ∂sourceMeasure (depth + (age + 1)), point ∉ bad age depth → dist point (first age depth (ownership age depth point)) ≤ mesh age)
    (badConvergence : ∀ age, Tendsto (fun depth => sourceMeasure (depth + (age + 1)) (bad age depth)) atTop (𝓝 0))
    (weightConvergence : ∀ age, Tendsto (fun depth => levyProkhorovEDist
      ((sourceMeasure (depth + (age + 1))).map (fun point => second age (ownership age depth point))) (projection age)) atTop (𝓝 0))
    (projectionConvergence : Tendsto (fun age => levyProkhorovEDist (projection age) targetMeasure) atTop (𝓝 0))
    (markIndex : ∀ age, Bool → Index age)
    (firstMarks : ∀ age, ∀ᶠ depth in atTop, ∀ side, first age depth (markIndex age side) = sourceMark (depth + (age + 1)) side)
    (secondMarks : ∀ age side, second age (markIndex age side) = targetMark side) :
    MarkedGHPConverges Source sourceMeasure targetMeasure sourceMark targetMark := by
  intro epsilon epsilonPositive
  have meshSmall := (tendsto_order.mp meshConvergence).2 (epsilon / 8) (by positivity)
  have projectionSmall := (tendsto_order.mp projectionConvergence).2
    (ENNReal.ofReal (epsilon / 4)) (by positivity)
  obtain ⟨age, ageLarge, meshSmall, projectionSmall⟩ :=
    ((eventually_ge_atTop start).and (meshSmall.and projectionSmall)).exists
  have errorConvergence := (badConvergence age).add (weightConvergence age)
  simp only [zero_add] at errorConvergence
  have errorSmall := (tendsto_order.mp errorConvergence).2 (ENNReal.ofReal (epsilon / 4)) (by positivity)
  rw [← map_add_atTop_eq_nat (age + 1)]
  change ∀ᶠ depth in atTop, _

  filter_upwards [firstNet age ageLarge, distortion age (epsilon / 8) (by positivity),
    close age ageLarge, errorSmall, firstMarks age] with depth firstNet distortion close errorSmall firstMarks
  obtain ⟨common, firstIsometry, secondIsometry, matched, hausdorff, transport⟩ :=
    exists_common_metric_measure_of_projection (first age depth) (second age)
      (sourceMeasure (depth + (age + 1))) (projection age) targetMeasure (ownership age depth)
      (projectionMeasurable age depth) (bad age depth) (mesh age) (mesh age) (mesh age) (epsilon / 8)
      (meshNonnegative age) (meshNonnegative age) (meshNonnegative age) (by positivity)
      firstNet (secondNet age ageLarge) distortion close
  letI := common
  letI : TopologicalSpace (Source (depth + (age + 1)) ⊕ Target) := common.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Source (depth + (age + 1)) ⊕ Target) := borel (Source (depth + (age + 1)) ⊕ Target)
  refine ⟨common, firstIsometry, secondIsometry, hausdorff.trans_lt (by linarith), ?_, ?_⟩
  · calc
      _ ≤ ENNReal.ofReal (mesh age + epsilon / 8) + sourceMeasure (depth + (age + 1)) (bad age depth) +
          levyProkhorovEDist ((sourceMeasure (depth + (age + 1))).map (fun point => second age (ownership age depth point))) (projection age) +
          levyProkhorovEDist (projection age) targetMeasure := transport
      _ = ENNReal.ofReal (mesh age + epsilon / 8) +
          (sourceMeasure (depth + (age + 1)) (bad age depth) +
            levyProkhorovEDist ((sourceMeasure (depth + (age + 1))).map (fun point => second age (ownership age depth point))) (projection age)) +
          levyProkhorovEDist (projection age) targetMeasure := by ac_rfl
      _ ≤ ENNReal.ofReal (epsilon / 4) + ENNReal.ofReal (epsilon / 4) + ENNReal.ofReal (epsilon / 4) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal (by linarith)) errorSmall.le) projectionSmall.le
      _ = ENNReal.ofReal (3 * epsilon / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ < ENNReal.ofReal epsilon := (ENNReal.ofReal_lt_ofReal_iff epsilonPositive).mpr (by linarith)
  · intro side
    have equality := matched (markIndex age side)
    rw [firstMarks side, secondMarks age side] at equality
    exact equality.trans_lt (by linarith : epsilon / 8 < epsilon)

end
end IGSIII.Geometry
