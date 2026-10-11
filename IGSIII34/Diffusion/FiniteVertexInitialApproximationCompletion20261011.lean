import IGSIII34.Diffusion.CountableTimeLimitsCompletion20261011
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- Full support of the true limiting mass forces original finite vertex
placements to approximate every point, at every sufficiently high level. -/
theorem finiteVertex_eventually_approximates_completion20261011
    (Vertices : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (mass : ∀ depth, ProbabilityMeasure (Vertices depth))
    (placement : ∀ depth, Vertices depth → Space)
    (limit : ProbabilityMeasure Space) [(limit : Measure Space).IsOpenPosMeasure]
    (weak : Tendsto (fun depth => (mass depth).map (measurable_of_finite (placement depth)).aemeasurable)
      atTop (𝓝 limit)) (point : Space) (radius : ℝ) (radiusPositive : 0 < radius) :
    ∀ᶠ depth in atTop, ∃ vertex : Vertices depth, dist (placement depth vertex) point < radius := by
  by_contra failure
  have frequent : ∃ᶠ depth in atTop, ¬∃ vertex : Vertices depth, dist (placement depth vertex) point < radius := by
    simpa only [Filter.Frequently, not_not] using failure
  obtain ⟨selected, strict, absent⟩ := extraction_of_frequently_atTop frequent
  have zeroMeasure (index : ℕ) :
      (((mass (selected index)).map (measurable_of_finite (placement (selected index))).aemeasurable : ProbabilityMeasure Space) : Measure Space)
        (Metric.ball point radius) = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_of_finite _) Metric.isOpen_ball.measurableSet]
    have empty : (placement (selected index)) ⁻¹' Metric.ball point radius = ∅ := by
      ext vertex
      simp only [mem_preimage, Metric.mem_ball, mem_empty_iff_false, iff_false]
      exact not_exists.mp (absent index) vertex
    rw [empty, measure_empty]
  have lower := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (weak.comp strict.tendsto_atTop) (Metric.isOpen_ball (x := point) (ε := radius))
  have positive := Metric.measure_ball_pos (limit : Measure Space) point radiusPositive
  have impossible : (limit : Measure Space) (Metric.ball point radius) ≤ 0 := by
    change (limit : Measure Space) (Metric.ball point radius) ≤ Filter.liminf
      (fun index => ((((mass (selected index)).map
        (measurable_of_finite (placement (selected index))).aemeasurable : ProbabilityMeasure Space) : Measure Space)
          (Metric.ball point radius))) atTop at lower
    simpa only [zeroMeasure, Filter.liminf_const] using lower
  exact not_le_of_gt positive impossible

/-- Every initial point has a genuine sequence of original finite
vertices converging to it. Their placed Dirac laws also converge. -/
theorem exists_finiteVertex_initial_approximation_completion20261011
    (Vertices : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (mass : ∀ depth, ProbabilityMeasure (Vertices depth))
    (placement : ∀ depth, Vertices depth → Space)
    (limit : ProbabilityMeasure Space) [(limit : Measure Space).IsOpenPosMeasure]
    (weak : Tendsto (fun depth => (mass depth).map (measurable_of_finite (placement depth)).aemeasurable)
      atTop (𝓝 limit)) (point : Space) :
    ∃ selected : ∀ depth, Vertices depth,
      Tendsto (fun depth => placement depth (selected depth)) atTop (𝓝 point) ∧
      Tendsto (fun depth => diracProba (placement depth (selected depth))) atTop (𝓝 (diracProba point)) := by
  classical
  letI : ∀ depth, Nonempty (Vertices depth) := fun depth => nonempty_of_isProbabilityMeasure (mass depth : Measure (Vertices depth))
  choose selected membership minimal using fun depth =>
    Finset.exists_min_image (Finset.univ : Finset (Vertices depth))
      (fun vertex => dist (placement depth vertex) point) Finset.univ_nonempty
  have convergence : Tendsto (fun depth => placement depth (selected depth)) atTop (𝓝 point) := by
    apply Metric.tendsto_nhds.mpr
    intro radius positive
    filter_upwards [finiteVertex_eventually_approximates_completion20261011 Vertices mass placement limit weak point radius positive]
      with depth approximation
    obtain ⟨vertex, close⟩ := approximation
    exact (minimal depth vertex (Finset.mem_univ vertex)).trans_lt close
  exact ⟨selected, convergence, continuous_diracProba.continuousAt.tendsto.comp convergence⟩

end
end IGSIII34.Diffusion
