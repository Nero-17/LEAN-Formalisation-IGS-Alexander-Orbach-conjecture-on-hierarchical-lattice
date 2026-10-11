import IGSIII34.Diffusion.CountableDistanceProfile
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set UniformSpace
open scoped Topology Uniformity

/-- Countable observation laws transfer under the same uniform spatial
profile approximation as the separately proved full-càdlàg transfer. -/
theorem countableProfileObservation_weak_transfer
    {Labels Target : Type*} [Countable Labels] [MetricSpace Target] [SecondCountableTopology Target]
    [MeasurableSpace Target] [BorelSpace Target]
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (births : Labels → Target)
    (originals : ∀ depth, Outcomes depth → ℕ → CountableDistanceProfile Labels)
    (projections : ∀ depth, Outcomes depth → ℕ → Target)
    (originalsMeasurable : ∀ depth, AEMeasurable (originals depth) (laws depth))
    (projectionsMeasurable : ∀ depth, AEMeasurable (projections depth) (laws depth))
    (law : ProbabilityMeasure (ℕ → Target))
    (projectedWeak : Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
      (projectionsMeasurable depth)) atTop (𝓝 law))
    (coordinateClose : ∀ time label tolerance, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ outcome, dist (originals depth outcome time label)
        (distanceProfilePoint births (projections depth outcome time) label) < tolerance) :
    Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth)) (originalsMeasurable depth)) atTop
      (𝓝 (law.map (show AEMeasurable
        (fun observation : ℕ → Target => fun time => distanceProfilePoint births (observation time)) law from
        (continuous_pi (fun time => (distanceProfilePoint_continuous births).comp
          (continuous_apply time))).measurable.aemeasurable))) := by
  classical
  letI : MetricSpace (ℕ → CountableDistanceProfile Labels) := UniformSpace.metricSpace _
  let carrier : (ℕ → Target) → (ℕ → CountableDistanceProfile Labels) :=
    fun observation time => distanceProfilePoint births (observation time)
  have carrierContinuous : Continuous carrier :=
    continuous_pi (fun time => (distanceProfilePoint_continuous births).comp (continuous_apply time))
  let approximations := fun depth outcome => carrier (projections depth outcome)
  have approximationsMeasurable (depth : ℕ) : AEMeasurable (approximations depth) (laws depth) :=
    carrierContinuous.measurable.comp_aemeasurable (projectionsMeasurable depth)
  have mapIdentity (depth : ℕ) :
      ((ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        (projectionsMeasurable depth)).map carrierContinuous.measurable.aemeasurable) =
      ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (Outcomes depth))
        (approximationsMeasurable depth) := by
    apply Subtype.ext
    exact AEMeasurable.map_map_of_aemeasurable carrierContinuous.measurable.aemeasurable
      (projectionsMeasurable depth)
  have weakApproximations :=
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ law projectedWeak carrierContinuous).congr'
      (Eventually.of_forall mapIdentity)
  apply probability_ae_sample_weak_transfer_completion20261011 laws (law : Measure (ℕ → Target))
    originals approximations carrier originalsMeasurable approximationsMeasurable
    carrierContinuous.measurable.aemeasurable weakApproximations
  intro tolerance error positive errorPositive
  have entourage := Metric.dist_mem_uniformity (α := ℕ → CountableDistanceProfile Labels) positive
  rw [Pi.uniformity] at entourage
  obtain ⟨coordinates, entourage⟩ := (mem_iInf_finite _).mp entourage
  obtain ⟨sets, membership, equality⟩ := mem_iInf_finset.mp entourage
  have eventuallyCoordinates : ∀ᶠ depth in atTop, ∀ time ∈ coordinates,
      ∀ outcome, (originals depth outcome, approximations depth outcome) ∈ sets time := by
    apply coordinates.eventually_all.mpr
    intro time member
    obtain ⟨coordinateSet, coordinateMember, subset⟩ := mem_comap.mp (membership time member)
    obtain ⟨coordinateTolerance, coordinatePositive, coordinateBound⟩ :=
      Metric.mem_uniformity_dist.mp coordinateMember
    have uniform := countableDistanceProfile_uniform_of_coordinate_uniform Outcomes
      (fun depth outcome => originals depth outcome time)
      (fun depth outcome => distanceProfilePoint births (projections depth outcome time))
      (coordinateClose time) coordinateTolerance coordinatePositive
    filter_upwards [uniform] with depth close
    intro outcome
    exact subset (coordinateBound (close outcome))
  filter_upwards [eventuallyCoordinates] with depth close
  refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
  · simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using errorPositive.le
  · intro outcome _
    have member : (originals depth outcome, approximations depth outcome) ∈
        ⋂ time ∈ coordinates, sets time :=
      mem_iInter.mpr (fun time => mem_iInter.mpr (fun member => close time member outcome))
    rw [← equality] at member
    exact member.le

end
end IGSIII34.Diffusion
