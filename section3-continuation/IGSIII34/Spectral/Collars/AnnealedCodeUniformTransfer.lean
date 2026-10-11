import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCoding
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion20261011
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality MeasureTheory Filter ProbabilityTheory
open scoped Uniformity _root_.Topology

instance actualAnnealedFiniteCodeUniform (rule : Rule) : UniformSpace (ActualAnnealedFiniteCode rule) :=
  inferInstanceAs (UniformSpace (((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))

instance actualAnnealedFiniteCodeUniformCountablyGenerated (rule : Rule) :
    IsCountablyGenerated (𝓤 (ActualAnnealedFiniteCode rule)) :=
  inferInstanceAs (IsCountablyGenerated (𝓤 ((((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))))

instance actualAnnealedFiniteCodeMetric (rule : Rule) : MetricSpace (ActualAnnealedFiniteCode rule) :=
  UniformSpace.metricSpace _

theorem uniform_real_coordinate_pairs_tendsto
    (Samples : ℕ → Type*) (first second : ∀ depth, Samples depth → ℝ)
    (close : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |first depth sample - second depth sample| < tolerance) :
    Tendsto (fun sample : Σ depth, Samples depth => (first sample.1 sample.2, second sample.1 sample.2))
      (comap Sigma.fst atTop) (𝓤 ℝ) := by
  apply Metric.uniformity_basis_dist.tendsto_right_iff.mpr
  intro tolerance positive
  apply eventually_comap.mpr
  filter_upwards [close tolerance positive] with depth close
  rintro ⟨age, sample⟩ same
  cases same
  exact (Real.dist_eq _ _).symm ▸ close sample

/-- Coordinatewise uniform approximation is uniform approximation in the
fixed countable product code, regardless of the changing finite sample domains. -/
theorem actualAnnealedFiniteCode_coordinate_uniform_close
    (rule : Rule) (Samples : ℕ → Type*)
    (codes approximations : ∀ depth, Samples depth → ActualAnnealedFiniteCode rule)
    (geometry : ∀ label, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).1 label - (approximations depth sample).1 label| < tolerance)
    (mass : ∀ counting labels, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).2.1 counting labels - (approximations depth sample).2.1 counting labels| < tolerance)
    (paths : ∀ time label, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).2.2 time label - (approximations depth sample).2.2 time label| < tolerance) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, dist (codes depth sample) (approximations depth sample) < tolerance := by
  have pairs : Tendsto (fun sample : Σ depth, Samples depth =>
      (codes sample.1 sample.2, approximations sample.1 sample.2))
      (comap Sigma.fst atTop) (𝓤 (ActualAnnealedFiniteCode rule)) := by
    change Tendsto _ _ (𝓤 ((((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
      (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ))))
    simp only [uniformity_prod, tendsto_inf, tendsto_comap_iff, Pi.uniformity,
      tendsto_iInf, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩
    · intro label
      exact uniform_real_coordinate_pairs_tendsto Samples _ _ (geometry label)
    · intro counting labels
      exact uniform_real_coordinate_pairs_tendsto Samples _ _ (mass counting labels)
    · intro time label
      exact uniform_real_coordinate_pairs_tendsto Samples _ _ (paths time label)
  intro tolerance positive
  have member : {pair : ActualAnnealedFiniteCode rule × ActualAnnealedFiniteCode rule | dist pair.1 pair.2 < tolerance} ∈ 𝓤 (ActualAnnealedFiniteCode rule) :=
    Metric.uniformity_basis_dist.mem_iff.mpr ⟨tolerance, positive, Set.Subset.rfl⟩
  have eventually := pairs.eventually member
  have fromDepth := eventually_comap.mp eventually
  filter_upwards [fromDepth] with depth close
  intro sample
  exact close ⟨depth,sample⟩ rfl

/-- The fixed coding map of a quenched limit and the genuinely encoded
finite samples have the same weak limit once all actual coordinate errors vanish. -/
theorem actualAnnealedFiniteCode_weak_transfer
    (rule : Rule) {Space : Type*} [TopologicalSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Samples : ℕ → Type*) [∀ depth, MeasurableSpace (Samples depth)]
    (laws : ∀ depth, Measure (Samples depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (limitLaw : ProbabilityMeasure Space)
    (placements : ∀ depth, Samples depth → Space)
    (placementsMeasurable : ∀ depth, AEMeasurable (placements depth) (laws depth))
    (weak : Tendsto (fun depth => ProbabilityMeasure.map (⟨laws depth,inferInstance⟩ : ProbabilityMeasure (Samples depth))
      (placementsMeasurable depth)) atTop (𝓝 limitLaw))
    (limitCode : Space → ActualAnnealedFiniteCode rule) (limitContinuous : Continuous limitCode)
    (codes : ∀ depth, Samples depth → ActualAnnealedFiniteCode rule)
    (codesMeasurable : ∀ depth, AEMeasurable (codes depth) (laws depth))
    (geometry : ∀ label, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).1 label - (limitCode (placements depth sample)).1 label| < tolerance)
    (mass : ∀ counting labels, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).2.1 counting labels - (limitCode (placements depth sample)).2.1 counting labels| < tolerance)
    (paths : ∀ time label, ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |(codes depth sample).2.2 time label - (limitCode (placements depth sample)).2.2 time label| < tolerance) :
    Tendsto (fun depth => ProbabilityMeasure.map (⟨laws depth,inferInstance⟩ : ProbabilityMeasure (Samples depth))
      (codesMeasurable depth)) atTop (𝓝 (ProbabilityMeasure.map limitLaw limitContinuous.measurable.aemeasurable)) := by
  have approximateMeasurable (depth : ℕ) : AEMeasurable (limitCode ∘ placements depth) (laws depth) :=
    limitContinuous.measurable.comp_aemeasurable (placementsMeasurable depth)
  have approximateWeak : Tendsto (fun depth => ProbabilityMeasure.map (⟨laws depth,inferInstance⟩ : ProbabilityMeasure (Samples depth))
      (approximateMeasurable depth)) atTop (𝓝 (ProbabilityMeasure.map limitLaw limitContinuous.measurable.aemeasurable)) := by
    have mapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ weak limitContinuous
    apply mapped.congr'
    apply Eventually.of_forall
    intro depth
    apply ProbabilityMeasure.toMeasure_injective
    exact AEMeasurable.map_map_of_aemeasurable limitContinuous.measurable.aemeasurable (placementsMeasurable depth)
  apply IGSIII34.Diffusion.probability_ae_sample_weak_transfer_completion20261011 laws
    (limitLaw : Measure Space) codes (fun depth => limitCode ∘ placements depth) limitCode
    codesMeasurable approximateMeasurable limitContinuous.measurable.aemeasurable approximateWeak
  intro tolerance error positive errorPositive
  filter_upwards [actualAnnealedFiniteCode_coordinate_uniform_close rule Samples codes
    (fun depth => limitCode ∘ placements depth) geometry mass paths tolerance positive] with depth close
  refine ⟨∅, MeasurableSet.empty, ?_, fun sample _ => (close sample).le⟩
  simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using errorPositive.le

end
end IGSIII34.Spectral
