import IGSIII34.Diffusion.CountableDistanceProfile
import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion20261011
import IGSIII34.Diffusion.UsualLocalJ1PathLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

/-- Every original time of every original path is retained by the compact
countable spatial profile. Coordinatewise uniform spatial approximation
transfers whole integer-J1 and whole usual-local J1 weak convergence. -/
theorem countableDistanceProfile_whole_cadlag_weak
    {Labels Target : Type*} [Countable Labels] [MetricSpace Target] [CompactSpace Target]
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (births : Labels → Target)
    (originals : ∀ depth, Outcomes depth →
      SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile Labels))
    (projections : ∀ depth, Outcomes depth → SkorokhodCadlagPathCompletion20261011 Target)
    (originalsMeasurable : ∀ depth, AEMeasurable (originals depth) (laws depth))
    (projectionsMeasurable : ∀ depth, AEMeasurable (projections depth) (laws depth))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Target))
    (projectedWeak : Tendsto (fun depth =>
      ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        (projectionsMeasurable depth)) atTop (𝓝 law))
    (coordinateClose : ∀ label tolerance, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ outcome time,
        dist ((originals depth outcome).val time label)
          (distanceProfilePoint births ((projections depth outcome).val time) label) < tolerance) :
    Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth)) (originalsMeasurable depth))
      atTop (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (distanceProfilePoint births) (distanceProfilePoint_continuous births)).measurable.aemeasurable)) ∧
    Tendsto (fun depth => usualLocalJ1PathProbability (ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth)) (originalsMeasurable depth)))
      atTop (𝓝 (usualLocalJ1PathProbability (law.map
        (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
          (distanceProfilePoint births) (distanceProfilePoint_continuous births)).measurable.aemeasurable))) := by
  have placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ outcome time, dist ((originals depth outcome).val time)
        (distanceProfilePoint births ((projections depth outcome).val time)) < tolerance := by
    intro tolerance positive
    have uniform := countableDistanceProfile_uniform_of_coordinate_uniform
      (fun depth => Outcomes depth × ℝ≥0)
      (fun depth pair => (originals depth pair.1).val pair.2)
      (fun depth pair => distanceProfilePoint births ((projections depth pair.1).val pair.2))
      (fun label tolerance positive => (coordinateClose label tolerance positive).mono
        (fun depth close pair => close pair.1 pair.2)) tolerance positive
    exact uniform.mono (fun depth close outcome time => close (outcome, time))
  have weak := common_embedding_cadlag_sample_weak_completion20261011
    Outcomes laws (distanceProfilePoint births) (distanceProfilePoint_continuous births)
    originals projections originalsMeasurable projectionsMeasurable law projectedWeak placementClose
  exact ⟨weak, integerJ1_weak_to_usualLocalJ1 _ _ weak⟩

end
end IGSIII34.Diffusion
