import IGSIII34.Diffusion.FiniteStoppingExitCompletion20261011
import Mathlib.Probability.Martingale.OptionalSampling

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

theorem finiteWalk_compensated_window_lower_completion20261011
    (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (first last window : ℕ) (ordered : first ≤ last) (lengthBound : last ≤ first + window)
    (path : ℕ → Vertex) :
    potential (path first) + walkCompensatedPotential endpoint potential last path -
      walkCompensatedPotential endpoint potential first path - window * driftBound ≤ potential (path last) := by
  have split : (∑ index ∈ Finset.range last, rateOneGenerator endpoint potential (path index)) =
      (∑ index ∈ Finset.range first, rateOneGenerator endpoint potential (path index)) +
        ∑ index ∈ Finset.range (last - first), rateOneGenerator endpoint potential (path (first + index)) := by
    conv_lhs => rw [← Nat.add_sub_of_le ordered]
    exact Finset.sum_range_add _ _ _
  have lower : -(window * driftBound) ≤
      ∑ index ∈ Finset.range (last - first), rateOneGenerator endpoint potential (path (first + index)) := by
    have duration : last - first ≤ window := by omega
    calc
      _ ≤ -((last - first : ℕ) * driftBound) := by
        exact neg_le_neg (mul_le_mul_of_nonneg_right (by exact_mod_cast duration) driftNonnegative)
      _ = ∑ _index ∈ Finset.range (last - first), -driftBound := by simp
      _ ≤ _ := Finset.sum_le_sum fun index _ => (abs_le.mp (generatorBound (path (first + index)))).1
  unfold walkCompensatedPotential
  rw [split]
  linarith

/-- Conditional optional sampling gives a genuine bound after any bounded
stopping time, tested on every event known at that stopping time. The bound
depends on the duration of the new window, rather than the elapsed past. -/
theorem finiteDiscreteWalkLaw_stopping_window_lower_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (first last : (ℕ → Vertex) → WithTop ℕ)
    (firstStopping : IsStoppingTime Filtration.piLE first)
    (lastStopping : IsStoppingTime Filtration.piLE last)
    (ordered : first ≤ last) (horizon window : ℕ) (bounded : ∀ path, last path ≤ horizon)
    (lengthBound : ∀ path, (last path).untopA ≤ (first path).untopA + window)
    (event : Set (ℕ → Vertex)) (known : MeasurableSet[firstStopping.measurableSpace] event) :
    (∫ path in event, stoppedValue (fun index path => potential (path index)) first path
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) -
      window * driftBound * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real event ≤
    ∫ path in event, stoppedValue (fun index path => potential (path index)) last path
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have firstBounded : ∀ path, first path ≤ horizon := fun path => (ordered path).trans (bounded path)
  have martingale := finiteDiscreteWalkLaw_compensated_martingale endpoint positiveDegree initial potential
  have firstMIntegrable := martingale.submartingale.integrable_stoppedValue firstStopping firstBounded
  have lastMIntegrable := martingale.submartingale.integrable_stoppedValue lastStopping bounded
  have firstIntegrable := integrable_stoppedValue ℕ firstStopping
    (fun index => (finitePathPotential_memLp_completion20261011 law potential index 1).integrable le_rfl) firstBounded
  have lastIntegrable := integrable_stoppedValue ℕ lastStopping
    (fun index => (finitePathPotential_memLp_completion20261011 law potential index 1).integrable le_rfl) bounded
  have sampling := martingale.stoppedValue_ae_eq_condExp_of_le lastStopping firstStopping ordered bounded
  have martingaleEquality :
      (∫ path in event, stoppedValue (walkCompensatedPotential endpoint potential) first path ∂law) =
      ∫ path in event, stoppedValue (walkCompensatedPotential endpoint potential) last path ∂law := by
    calc
      _ = ∫ path in event, (law[stoppedValue (walkCompensatedPotential endpoint potential) last |
          firstStopping.measurableSpace]) path ∂law :=
        setIntegral_congr_ae (firstStopping.measurableSpace_le event known)
          (sampling.mono fun path equality _ => equality)
      _ = _ := setIntegral_condExp firstStopping.measurableSpace_le lastMIntegrable known
  have pointwise (path : ℕ → Vertex) :
      stoppedValue (fun index path => potential (path index)) first path +
        stoppedValue (walkCompensatedPotential endpoint potential) last path -
        stoppedValue (walkCompensatedPotential endpoint potential) first path - window * driftBound ≤
      stoppedValue (fun index path => potential (path index)) last path := by
    have firstFinite : first path ≠ ⊤ := by
      intro equality
      have contradiction := firstBounded path
      simp [equality] at contradiction
    have lastFinite : last path ≠ ⊤ := by
      intro equality
      have contradiction := bounded path
      simp [equality] at contradiction
    have countsOrdered : (first path).untopA ≤ (last path).untopA := by
      lift first path to ℕ using firstFinite with firstCount firstEquality
      lift last path to ℕ using lastFinite with lastCount lastEquality
      have comparison := ordered path
      rw [← firstEquality, ← lastEquality] at comparison
      exact WithTop.coe_le_coe.mp comparison
    exact finiteWalk_compensated_window_lower_completion20261011 endpoint potential driftBound
      driftNonnegative generatorBound _ _ window countsOrdered (lengthBound path) path
  have comparison := integral_mono (μ := law.restrict event)
    (((firstIntegrable.add lastMIntegrable).sub firstMIntegrable).sub (integrable_const _)).integrableOn
    lastIntegrable.integrableOn pointwise
  have split :
      (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
        stoppedValue (walkCompensatedPotential endpoint potential) last path -
        stoppedValue (walkCompensatedPotential endpoint potential) first path - window * driftBound ∂law) =
      (∫ path in event, stoppedValue (fun index path => potential (path index)) first path ∂law) -
        window * driftBound * law.real event := by
    have subtractConstant :
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
          stoppedValue (walkCompensatedPotential endpoint potential) last path -
          stoppedValue (walkCompensatedPotential endpoint potential) first path - window * driftBound ∂law) =
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
          stoppedValue (walkCompensatedPotential endpoint potential) last path -
          stoppedValue (walkCompensatedPotential endpoint potential) first path ∂law) -
          ∫ _path in event, window * driftBound ∂law :=
      integral_sub ((firstIntegrable.add lastMIntegrable).sub firstMIntegrable).integrableOn (integrable_const _)
    have subtractFirst :
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
          stoppedValue (walkCompensatedPotential endpoint potential) last path -
          stoppedValue (walkCompensatedPotential endpoint potential) first path ∂law) =
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
          stoppedValue (walkCompensatedPotential endpoint potential) last path ∂law) -
          ∫ path in event, stoppedValue (walkCompensatedPotential endpoint potential) first path ∂law :=
      integral_sub (firstIntegrable.add lastMIntegrable).integrableOn firstMIntegrable.integrableOn
    have addLast :
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
          stoppedValue (walkCompensatedPotential endpoint potential) last path ∂law) =
        (∫ path in event, stoppedValue (fun index path => potential (path index)) first path ∂law) +
          ∫ path in event, stoppedValue (walkCompensatedPotential endpoint potential) last path ∂law :=
      integral_add firstIntegrable.integrableOn lastMIntegrable.integrableOn
    rw [subtractConstant, subtractFirst, addLast]
    rw [martingaleEquality]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    ring
  change (∫ path in event, stoppedValue (fun index path => potential (path index)) first path +
    stoppedValue (walkCompensatedPotential endpoint potential) last path -
    stoppedValue (walkCompensatedPotential endpoint potential) first path - window * driftBound ∂law) ≤ _ at comparison
  rw [split] at comparison
  exact comparison

end
end IGSIII34.Diffusion
