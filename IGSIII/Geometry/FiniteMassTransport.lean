import IGSIII.Geometry.ProjectionTransport
import Universality.Probability.FiniteWeightMeasure

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace IGSIII.Geometry
noncomputable section

open Universality MeasureTheory ProbabilityTheory Metric Filter
open scoped BigOperators ENNReal Topology

variable {Alphabet Space : Type*} [Fintype Alphabet] [MeasurableSpace Alphabet] [MeasurableSingletonClass Alphabet]
  [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem finiteWeightPMF_measure_le_add_total_error (weight other : Alphabet → ℝ)
    (nonnegative : ∀ letter, 0 ≤ weight letter) (other_nonnegative : ∀ letter, 0 ≤ other letter)
    (mass_one : ∑ letter, weight letter = 1) (other_mass_one : ∑ letter, other letter = 1)
    (event : Set Alphabet) :
    (finiteWeightPMF weight nonnegative mass_one).toMeasure event ≤
      (finiteWeightPMF other other_nonnegative other_mass_one).toMeasure event +
        ∑ letter, ENNReal.ofReal |weight letter - other letter| := by
  classical
  rw [PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro letter _
  by_cases membership : letter ∈ event
  · simp only [Set.indicator_of_mem membership, finiteWeightPMF_apply]
    rw [← ENNReal.ofReal_add (other_nonnegative letter) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self (weight letter - other letter)]
  · simp only [Set.indicator_of_notMem membership]
    exact bot_le

theorem levyProkhorovEDist_finiteWeightPMF_map_le (weight other : Alphabet → ℝ)
    (nonnegative : ∀ letter, 0 ≤ weight letter) (other_nonnegative : ∀ letter, 0 ≤ other letter)
    (mass_one : ∑ letter, weight letter = 1) (other_mass_one : ∑ letter, other letter = 1)
    (anchor : Alphabet → Space) (measurable : Measurable anchor) :
    levyProkhorovEDist ((finiteWeightPMF weight nonnegative mass_one).toMeasure.map anchor)
      ((finiteWeightPMF other other_nonnegative other_mass_one).toMeasure.map anchor) ≤
        ∑ letter, ENNReal.ofReal |weight letter - other letter| := by
  apply levyProkhorovEDist_le_of_forall
  intro epsilon event error_lt epsilon_finite event_measurable
  have epsilon_positive : 0 < epsilon.toReal :=
    ENNReal.toReal_pos (ne_of_gt (bot_le.trans_lt error_lt)) epsilon_finite.ne
  have inclusion : event ⊆ Metric.thickening epsilon.toReal event := by
    intro point membership
    exact Metric.mem_thickening_iff.mpr ⟨point, membership, by simpa using epsilon_positive⟩
  constructor
  · have bound := finiteWeightPMF_measure_le_add_total_error weight other nonnegative other_nonnegative
      mass_one other_mass_one (anchor ⁻¹' event)
    rw [Measure.map_apply measurable event_measurable,
      Measure.map_apply measurable Metric.isOpen_thickening.measurableSet]
    apply bound.trans
    exact add_le_add (by
      apply measure_mono
      exact Set.preimage_mono inclusion) error_lt.le
  · have bound := finiteWeightPMF_measure_le_add_total_error other weight other_nonnegative nonnegative
      other_mass_one mass_one (anchor ⁻¹' event)
    simp_rw [abs_sub_comm (other _)] at bound
    rw [Measure.map_apply measurable event_measurable,
      Measure.map_apply measurable Metric.isOpen_thickening.measurableSet]
    apply bound.trans
    exact add_le_add (by
      apply measure_mono
      exact Set.preimage_mono inclusion) error_lt.le

/-- Coordinate convergence of finite probability weights gives Prokhorov
convergence after any fixed finite collection of actual anchors. -/
theorem levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero (weight : ℕ → Alphabet → ℝ) (limit_weight : Alphabet → ℝ)
    (nonnegative : ∀ depth letter, 0 ≤ weight depth letter) (limit_nonnegative : ∀ letter, 0 ≤ limit_weight letter)
    (mass_one : ∀ depth, ∑ letter, weight depth letter = 1) (limit_mass_one : ∑ letter, limit_weight letter = 1)
    (convergence : ∀ letter, Tendsto (fun depth => weight depth letter) atTop (𝓝 (limit_weight letter)))
    (anchor : Alphabet → Space) (measurable : Measurable anchor) :
    Tendsto (fun depth => levyProkhorovEDist
      ((finiteWeightPMF (weight depth) (nonnegative depth) (mass_one depth)).toMeasure.map anchor)
      ((finiteWeightPMF limit_weight limit_nonnegative limit_mass_one).toMeasure.map anchor)) atTop (𝓝 0) := by
  have error_convergence : Tendsto (fun depth => ∑ letter, |weight depth letter - limit_weight letter|) atTop (𝓝 0) := by
    have sums := tendsto_finsetSum Finset.univ (fun (letter : Alphabet) _ =>
      ((convergence letter).sub_const (limit_weight letter)).abs)
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using sums
  have ennreal_convergence : Tendsto (fun depth => ∑ letter, ENNReal.ofReal |weight depth letter - limit_weight letter|)
      atTop (𝓝 0) := by
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun letter _ => abs_nonneg (weight _ letter - limit_weight letter))]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp error_convergence
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ennreal_convergence
    (fun _ => bot_le) (fun depth => levyProkhorovEDist_finiteWeightPMF_map_le
      (weight depth) limit_weight (nonnegative depth) limit_nonnegative (mass_one depth) limit_mass_one anchor measurable)

end
end IGSIII.Geometry
