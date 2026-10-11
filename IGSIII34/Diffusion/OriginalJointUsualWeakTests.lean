import IGSIII34.Diffusion.OriginalJointCoupledUsualJ1
import IGSIII34.Diffusion.UsualLocalJ1WeakTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter MeasureTheory
open scoped Topology

/-- Sequential continuity for original joint GHP geometry and usual J1
paths, expressed through actual common-isometric-embedding couplings. -/
def OriginalJointUsualSequentiallyContinuousTest
    (test : OriginalJointCompactSpace → ℝ) : Prop :=
  ∀ (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit),
    OriginalJointCoupledUsualJ1Convergence sequence limit couplings →
    Tendsto (fun index => test (originalJointCompactClass (sequence index))) atTop
      (𝓝 (test (originalJointCompactClass limit)))

theorem originalJointUsualTest_continuousAt_continuous_representative
    (test : OriginalJointCompactSpace → ℝ)
    (usualContinuous : OriginalJointUsualSequentiallyContinuousTest test)
    (limit : OriginalJointCompactRepresentative)
    (limitContinuous : Continuous limit.path.val.toFun) :
    ContinuousAt test (originalJointCompactClass limit) := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro points convergence
  have representativeExists (index : ℕ) : ∃ representative : OriginalJointCompactRepresentative,
      originalJointCompactClass representative = points index :=
    SeparationQuotient.surjective_mk (points index)
  choose representatives identities using representativeExists
  have representativeConvergence : Tendsto (fun index => originalJointCompactClass (representatives index))
      atTop (𝓝 (originalJointCompactClass limit)) := by
    simpa only [identities] using convergence
  obtain ⟨couplings, coupledConvergence⟩ := originalJointCompactClass_tendsto_coupled_usualJ1
    representatives limit representativeConvergence limitContinuous
  convert usualContinuous representatives limit couplings coupledConvergence using 1
  funext index
  exact congrArg test (identities index).symm

/-- Genuine weak convergence in the constructed original metric implies
all bounded measurable usual joint tests when the limiting law has
continuous original path representatives almost everywhere. -/
theorem originalJointCompact_weak_usual_tests
    (laws : ℕ → ProbabilityMeasure OriginalJointCompactSpace)
    (law : ProbabilityMeasure OriginalJointCompactSpace)
    (weak : Tendsto laws atTop (𝓝 law))
    (continuousRepresentatives : ∀ᵐ point ∂(law : Measure OriginalJointCompactSpace),
      ∃ representative : OriginalJointCompactRepresentative,
        originalJointCompactClass representative = point ∧ Continuous representative.path.val.toFun)
    (test : OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ) (bounded : ∀ point, |test point| ≤ bound)
    (usualContinuous : OriginalJointUsualSequentiallyContinuousTest test) :
    Tendsto (fun index => ∫ point, test point ∂(laws index : Measure OriginalJointCompactSpace)) atTop
      (𝓝 (∫ point, test point ∂(law : Measure OriginalJointCompactSpace))) := by
  apply probability_weak_integral_bounded_ae_continuous laws law weak test measurable bound bounded
  filter_upwards [continuousRepresentatives] with point representative
  obtain ⟨representative, identity, continuous⟩ := representative
  rw [← identity]
  exact originalJointUsualTest_continuousAt_continuous_representative test usualContinuous representative continuous

end
end IGSIII34.Diffusion
