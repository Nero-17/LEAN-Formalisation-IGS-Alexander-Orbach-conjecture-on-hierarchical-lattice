import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal BoundedContinuousFunction

/-- An isometric subtype preserves and reflects weak probability-law
convergence. Bounded Lipschitz tests extend to the ambient pseudometric
space by McShane extension and clipping, so neither closedness of the
subtype nor separability of the ambient space is required. -/
theorem probability_subtype_weak_of_val_weak_completion
    {Ambient : Type*} [PseudoMetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (predicate : Ambient → Prop) (laws : ℕ → ProbabilityMeasure {value : Ambient // predicate value})
    (law : ProbabilityMeasure {value : Ambient // predicate value})
    (weak : Tendsto (fun index => (laws index).map measurable_subtype_coe.aemeasurable) atTop
      (𝓝 (law.map measurable_subtype_coe.aemeasurable))) :
    Tendsto laws atTop (𝓝 law) := by
  classical
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro function bounded lipschitz
  obtain ⟨constant, lipschitz⟩ := lipschitz
  let test : {value : Ambient // predicate value} →ᵇ ℝ :=
    {toFun := function, continuous_toFun := lipschitz.continuous, map_bounded' := bounded}
  let onSet : Ambient → ℝ := fun value => if member : predicate value then test ⟨value, member⟩ else 0
  have onSetLipschitz : LipschitzOnWith constant onSet {value | predicate value} := by
    intro first firstMember second secondMember
    change predicate first at firstMember
    change predicate second at secondMember
    simp only [onSet, dif_pos firstMember, dif_pos secondMember]
    change edist (function ⟨first, firstMember⟩) (function ⟨second, secondMember⟩) ≤ constant * edist first second
    exact lipschitz ⟨first, firstMember⟩ ⟨second, secondMember⟩
  obtain ⟨extension, extensionLipschitz, extensionIdentity⟩ := onSetLipschitz.extend_real
  let clipped : Ambient → ℝ := fun value => max (-‖test‖) (min ‖test‖ (extension value))
  have clippedLipschitz : LipschitzWith constant clipped :=
    (extensionLipschitz.const_min ‖test‖).const_max (-‖test‖)
  have clippedRange : Bornology.IsBounded (Set.range clipped) := by
    apply isCompact_Icc.isBounded.subset
    rintro value ⟨point, rfl⟩
    exact ⟨le_max_left _ _, max_le (by linarith [norm_nonneg test]) (min_le_left _ _)⟩
  let extendedTest : Ambient →ᵇ ℝ :=
    {toFun := clipped, continuous_toFun := clippedLipschitz.continuous, map_bounded' := Metric.isBounded_range_iff.mp clippedRange}
  have matching (value : {value : Ambient // predicate value}) : extendedTest value = function value := by
    have original : extension value = test value := by
      have equal := extensionIdentity value.property
      simpa only [onSet, dif_pos value.property] using equal.symm
    have bounds := BoundedContinuousFunction.norm_coe_le_norm test value
    rw [Real.norm_eq_abs, abs_le] at bounds
    change max (-‖test‖) (min ‖test‖ (extension value)) = test value
    rw [original, min_eq_right bounds.2, max_eq_right bounds.1]
  have mappedIntegral (probability : ProbabilityMeasure {value : Ambient // predicate value}) :
      (∫ value, extendedTest value ∂(probability.map measurable_subtype_coe.aemeasurable : Measure Ambient)) =
        ∫ value, function value ∂(probability : Measure {value : Ambient // predicate value}) := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map measurable_subtype_coe.aemeasurable extendedTest.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall matching
  have integralWeak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weak) extendedTest
  simpa only [mappedIntegral] using integralWeak

end
end IGSIII34.Diffusion
