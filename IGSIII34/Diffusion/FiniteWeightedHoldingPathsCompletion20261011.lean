import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion20261011
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion20261011
import IGSIII34.Diffusion.CountingClockDensityCompletion20261011
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators _root_.Topology

variable {Vertex : Type*} [Fintype Vertex] [Nonempty Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def weightedHoldingSampleCompletion20261011 (weight : Vertex → ℝ)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : (ℕ → Vertex) × (ℕ → ℝ) :=
  (sample.1, fun index => weight (sample.1 index) * sample.2 index)

theorem weightedHoldingSample_measurable_completion20261011 (weight : Vertex → ℝ) :
    Measurable (weightedHoldingSampleCompletion20261011 weight) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro index
  exact ((measurable_of_finite weight).comp ((measurable_pi_apply index).comp measurable_fst)).mul
    ((measurable_pi_apply index).comp measurable_snd)

def weightedHoldingSampleMeasurableEquivCompletion20261011 (weight : Vertex → ℝ) (positive : ∀ vertex, 0 < weight vertex) :
    ((ℕ → Vertex) × (ℕ → ℝ)) ≃ᵐ ((ℕ → Vertex) × (ℕ → ℝ)) where
  toFun := weightedHoldingSampleCompletion20261011 weight
  invFun sample := (sample.1, fun index => sample.2 index / weight (sample.1 index))
  left_inv sample := by
    apply Prod.ext
    · rfl
    · funext index
      simp [weightedHoldingSampleCompletion20261011, (positive (sample.1 index)).ne']
  right_inv sample := by
    apply Prod.ext
    · rfl
    · funext index
      dsimp only [weightedHoldingSampleCompletion20261011]
      field_simp [(positive (sample.1 index)).ne']
  measurable_toFun := weightedHoldingSample_measurable_completion20261011 weight
  measurable_invFun := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro index
    exact ((measurable_pi_apply index).comp measurable_snd).div
      ((measurable_of_finite weight).comp ((measurable_pi_apply index).comp measurable_fst))

theorem weightedHoldingSample_regular_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop) :
    ∀ᵐ sample ∂law, (∀ index, 0 < (weightedHoldingSampleCompletion20261011 weight sample).2 index) ∧
      Tendsto (cumulativeHoldingTime (weightedHoldingSampleCompletion20261011 weight sample).2) atTop atTop := by
  obtain ⟨vertex, _, minimal⟩ := Finset.exists_min_image (Finset.univ : Finset Vertex) weight Finset.univ_nonempty
  filter_upwards [regular] with sample clock
  refine ⟨fun index => mul_pos (weightPositive _) (clock.1 _), ?_⟩
  have lowerDiverges := clock.2.const_mul_atTop (weightPositive vertex)
  apply tendsto_atTop_mono _ lowerDiverges
  intro count
  rw [cumulativeHoldingTime, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  exact mul_le_mul_of_nonneg_right (minimal (sample.1 index) (Finset.mem_univ _)) (clock.1 index).le

theorem weightedHoldingSample_map_regular_completion20261011
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ))) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop) :
    ∀ᵐ sample ∂((law.map (weightedHoldingSample_measurable_completion20261011 weight).aemeasurable :
        ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ))) : Measure ((ℕ → Vertex) × (ℕ → ℝ))),
      (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop := by
  rw [ae_iff]
  change (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))).map
    (weightedHoldingSampleMeasurableEquivCompletion20261011 weight weightPositive)
    {sample | ¬ ((∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop)} = 0
  rw [(weightedHoldingSampleMeasurableEquivCompletion20261011 weight weightPositive).map_apply]
  exact ae_iff.mp (weightedHoldingSample_regular_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) weight weightPositive regular)

def weightedHoldingGlobalSampleCompletion20261011 {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    (weight : Vertex → ℝ) (scale : ℝ) (placement : Vertex → Space)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : SkorokhodGlobalPathCompletion20261011 Space :=
  holdingGlobalSkorokhodSampleCompletion20261011 scale placement (weightedHoldingSampleCompletion20261011 weight sample)

theorem weightedHoldingGlobalSample_aemeasurable_completion20261011
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ))) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    AEMeasurable (weightedHoldingGlobalSampleCompletion20261011 weight scale placement)
      (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) := by
  have mapped := holdingGlobalSkorokhodSample_aemeasurable_completion20261011
    (law.map (weightedHoldingSample_measurable_completion20261011 weight).aemeasurable : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (weightedHoldingSample_map_regular_completion20261011 law weight weightPositive regular) scale scalePositive placement
  exact mapped.comp_measurable (weightedHoldingSample_measurable_completion20261011 weight)

theorem finiteCountingClockDensity_positive_completion20261011
    {Edge : Type*} [Fintype Edge] [Nonempty Edge] [DecidableEq Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (vertex : Vertex) :
    0 < finiteCountingClockDensityCompletion20261011 endpoint vertex := by
  unfold finiteCountingClockDensityCompletion20261011
  exact div_pos (by positivity) (mul_pos (by positivity) (positiveDegree vertex))

end
end IGSIII34.Diffusion
