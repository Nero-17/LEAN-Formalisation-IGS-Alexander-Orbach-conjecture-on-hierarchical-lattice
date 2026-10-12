import IGSIII34.Diffusion.ConditionalStoppingWindowCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex]

/-- The real walk's short exit probability is bounded conditionally on
every event known at the starting stopping time. Both stopping values and
the martingale are evaluated on the genuine full discrete path law. -/
theorem finiteDiscreteWalkLaw_conditional_exit_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (potentialUpper : ∀ vertex, potential vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (first last : (ℕ → Vertex) → WithTop ℕ)
    (firstStopping : IsStoppingTime Filtration.piLE first)
    (lastStopping : IsStoppingTime Filtration.piLE last)
    (ordered : first ≤ last) (horizon window : ℕ) (bounded : ∀ path, last path ≤ horizon)
    (lengthBound : ∀ path, (last path).untopA ≤ (first path).untopA + window)
    (event : Set (ℕ → Vertex)) (known : MeasurableSet[firstStopping.measurableSpace] event)
    (error threshold : ℝ)
    (startBound : ∀ path ∈ event, 1 - error ≤ potential (path (first path).untopA))
    (exit : Set (ℕ → Vertex)) (exitMeasurable : MeasurableSet exit)
    (exitBound : ∀ path ∈ exit, potential (path (last path).untopA) ≤ threshold) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real (event ∩ exit) ≤
      (error + window * driftBound) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real event := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have eventMeasurable := firstStopping.measurableSpace_le event known
  have firstBounded : ∀ path, first path ≤ horizon := fun path => (ordered path).trans (bounded path)
  have firstIntegrable := integrable_stoppedValue ℕ firstStopping
    (fun index => (finitePathPotential_memLp_completion law potential index 1).integrable le_rfl) firstBounded
  have lastIntegrable := integrable_stoppedValue ℕ lastStopping
    (fun index => (finitePathPotential_memLp_completion law potential index 1).integrable le_rfl) bounded
  have deficitIntegrable := (integrable_const (1 : ℝ)).sub lastIntegrable
  have startIntegral := setIntegral_ge_of_const_le_real eventMeasurable (measure_ne_top _ _)
    startBound firstIntegrable.integrableOn
  have stoppingLower := finiteDiscreteWalkLaw_stopping_window_lower_completion
    endpoint positiveDegree initial potential driftBound driftNonnegative generatorBound first last
    firstStopping lastStopping ordered horizon window bounded lengthBound event known
  have hitDeficit : ∀ path ∈ event ∩ exit, 1 - threshold ≤ 1 - potential (path (last path).untopA) :=
    fun path member => by linarith [exitBound path member.2]
  have deficitOnExit : IntegrableOn (fun path => 1 - potential (path (last path).untopA)) (event ∩ exit) law :=
    deficitIntegrable.integrableOn
  have exitIntegral := setIntegral_ge_of_const_le_real (eventMeasurable.inter exitMeasurable)
    (measure_ne_top law (event ∩ exit)) hitDeficit deficitOnExit
  have enlarge := setIntegral_mono_set (μ := law) (s := event ∩ exit) (t := event)
    (f := fun path => 1 - potential (path (last path).untopA)) deficitIntegrable.integrableOn
    (Eventually.of_forall fun path => by
      change 0 ≤ 1 - potential (path (last path).untopA)
      linarith [potentialUpper (path (last path).untopA)])
    (Eventually.of_forall fun _path => And.left)
  have split :
      (∫ path in event, 1 - potential (path (last path).untopA) ∂law) =
      law.real event - ∫ path in event, stoppedValue (fun index path => potential (path index)) last path ∂law := by
    have subtract :
        (∫ path in event, 1 - potential (path (last path).untopA) ∂law) =
        (∫ _path in event, (1 : ℝ) ∂law) -
          ∫ path in event, stoppedValue (fun index path => potential (path index)) last path ∂law :=
      integral_sub (integrable_const _) lastIntegrable.integrableOn
    rw [subtract]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  rw [split] at enlarge
  change (1 - error) * law.real event ≤
    ∫ path in event, stoppedValue (fun index path => potential (path index)) first path ∂law at startIntegral
  change (1 - threshold) * law.real (event ∩ exit) ≤ _ at exitIntegral
  change (∫ path in event, stoppedValue (fun index path => potential (path index)) first path ∂law) -
    window * driftBound * law.real event ≤ _ at stoppingLower
  change (1 - threshold) * law.real (event ∩ exit) ≤ (error + window * driftBound) * law.real event
  linarith

end
end IGSIII34.Diffusion
