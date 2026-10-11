import IGSIII34.Diffusion.OriginalJointUsualWeakTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter MeasureTheory
open scoped Topology

/-- A direct sample-law version avoids requiring measurability of the
set of all classes admitting continuous original representatives. -/
theorem originalJointCompact_weak_usual_tests_sample
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : ProbabilityMeasure Outcome)
    (sample : Outcome → OriginalJointCompactRepresentative)
    (sampleMeasurable : Measurable (fun outcome => originalJointCompactClass (sample outcome)))
    (sampleContinuous : ∀ outcome, Continuous (sample outcome).path.val.toFun)
    (laws : ℕ → ProbabilityMeasure OriginalJointCompactSpace)
    (weak : Tendsto laws atTop
      (𝓝 (outcomeLaw.map sampleMeasurable.aemeasurable)))
    (test : OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ) (bounded : ∀ point, |test point| ≤ bound)
    (usualContinuous : OriginalJointUsualSequentiallyContinuousTest test) :
    Tendsto (fun index => ∫ point, test point ∂(laws index : Measure OriginalJointCompactSpace)) atTop
      (𝓝 (∫ point, test point ∂(outcomeLaw.map sampleMeasurable.aemeasurable :
        Measure OriginalJointCompactSpace))) := by
  apply probability_weak_integral_bounded_ae_continuous laws _ weak test measurable bound bounded
  change ∀ᵐ point ∂(outcomeLaw : Measure Outcome).map
    (fun outcome => originalJointCompactClass (sample outcome)), ContinuousAt test point
  rw [ae_map_iff sampleMeasurable.aemeasurable (measurableSet_of_continuousAt test)]
  exact Eventually.of_forall (fun outcome =>
    originalJointUsualTest_continuousAt_continuous_representative test usualContinuous
      (sample outcome) (sampleContinuous outcome))

end
end IGSIII34.Diffusion
