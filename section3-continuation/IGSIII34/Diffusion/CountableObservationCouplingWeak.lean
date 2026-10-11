import IGSIII34.Diffusion.CountableWeakFiniteMarginalsCompletion20261011
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

/-- A genuine spatial clock coupling on every compact time interval
transfers countable observation-law weak convergence. This is proved
directly from finite observation laws, without an evaluation-measurability
assumption on the whole J1 carrier. -/
theorem countableObservation_weak_of_compact_uniform_coupling
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (times : ℕ → ℝ≥0)
    (samples approximations : ∀ depth, Outcomes depth → ℝ≥0 → Space)
    (samplesMeasurable : ∀ depth time, Measurable (fun outcome => samples depth outcome time))
    (approximationsMeasurable : ∀ depth time, Measurable (fun outcome => approximations depth outcome time))
    (target : ProbabilityMeasure (ℕ → Space))
    (approximationWeak : Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
      ((measurable_pi_lambda _ (fun index => approximationsMeasurable depth (times index))).aemeasurable))
      atTop (𝓝 target))
    (coupling : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∀ᶠ depth in atTop, ∃ bad : Set (Outcomes depth), MeasurableSet bad ∧ (laws depth).real bad ≤ error ∧
        ∀ outcome, outcome ∉ bad → ∀ time : ℝ≥0, (time : ℝ) ≤ horizon →
          dist (samples depth outcome time) (approximations depth outcome time) ≤ tolerance) :
    Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
      ((measurable_pi_lambda _ (fun index => samplesMeasurable depth (times index))).aemeasurable))
      atTop (𝓝 target) := by
  apply countableTimeLaws_weak_of_finite_marginals_completion20261011
  intro count coordinates
  let select : (ℕ → Space) → (Fin count → Space) := fun path index => path (coordinates index)
  have selectContinuous : Continuous select := by fun_prop
  let originalFinite := fun depth outcome index => samples depth outcome (times (coordinates index))
  let approximateFinite := fun depth outcome index => approximations depth outcome (times (coordinates index))
  have originalFiniteMeasurable (depth : ℕ) : Measurable (originalFinite depth) :=
    measurable_pi_lambda _ (fun index => samplesMeasurable depth (times (coordinates index)))
  have approximateFiniteMeasurable (depth : ℕ) : Measurable (approximateFinite depth) :=
    measurable_pi_lambda _ (fun index => approximationsMeasurable depth (times (coordinates index)))
  have originalIdentity (depth : ℕ) :
      ((ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        ((measurable_pi_lambda _ (fun index => samplesMeasurable depth (times index))).aemeasurable)).map
        selectContinuous.measurable.aemeasurable) =
      ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        (originalFiniteMeasurable depth).aemeasurable := by
    apply Subtype.ext
    exact Measure.map_map selectContinuous.measurable
      (measurable_pi_lambda _ (fun index => samplesMeasurable depth (times index)))
  have approximateIdentity (depth : ℕ) :
      ((ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        ((measurable_pi_lambda _ (fun index => approximationsMeasurable depth (times index))).aemeasurable)).map
        selectContinuous.measurable.aemeasurable) =
      ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        (approximateFiniteMeasurable depth).aemeasurable := by
    apply Subtype.ext
    exact Measure.map_map selectContinuous.measurable
      (measurable_pi_lambda _ (fun index => approximationsMeasurable depth (times index)))
  have finiteApproximateWeak :=
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ target approximationWeak selectContinuous).congr'
      (Eventually.of_forall approximateIdentity)
  have finiteWeak := probability_ae_sample_weak_transfer_completion20261011 laws
    (target : Measure (ℕ → Space)) originalFinite approximateFinite select
    (fun depth => (originalFiniteMeasurable depth).aemeasurable)
    (fun depth => (approximateFiniteMeasurable depth).aemeasurable)
    selectContinuous.measurable.aemeasurable finiteApproximateWeak ?_
  · simp_rw [originalIdentity]
    convert finiteWeak using 1
    apply congrArg (fun probability : ProbabilityMeasure (Fin count → Space) => 𝓝 probability)
    apply Subtype.ext
    rfl
  · intro tolerance error positive errorPositive
    let horizon : ℕ := ⌈((Finset.univ.sup (fun index : Fin count => times (coordinates index)) : ℝ≥0) : ℝ)⌉₊
    filter_upwards [coupling horizon tolerance error positive errorPositive] with depth near
    obtain ⟨bad, measurableBad, probabilityBad, close⟩ := near
    refine ⟨bad, measurableBad, probabilityBad, ?_⟩
    intro outcome outside
    apply (dist_pi_le_iff positive.le).mpr
    intro index
    apply close outcome outside (times (coordinates index))
    exact (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun index : Fin count => times (coordinates index))
      (Finset.mem_univ index))).trans (Nat.le_ceil _)

end
end IGSIII34.Diffusion
