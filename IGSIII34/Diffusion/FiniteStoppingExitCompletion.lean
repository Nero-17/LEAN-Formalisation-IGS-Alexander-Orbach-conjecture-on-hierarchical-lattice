import IGSIII34.Diffusion.ResolventWalkOscillationCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex]

/-- This estimate holds at every bounded stopping time for the genuine
neighbour chain, from any initial probability measure. -/
theorem finiteDiscreteWalkLaw_stopped_potential_lower_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (stoppingTime : (ℕ → Vertex) → WithTop ℕ) (stopping : IsStoppingTime Filtration.piLE stoppingTime)
    (time : ℕ) (bounded : ∀ path, stoppingTime path ≤ time) :
    (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) - time * driftBound ≤
      ∫ path, stoppedValue (fun index path => potential (path index)) stoppingTime path
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  have martingale := finiteDiscreteWalkLaw_compensated_martingale endpoint positiveDegree initial potential
  have expectedMartingale := martingale.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const Filtration.piLE 0) stopping
    (fun path => bot_le) bounded
  change (∫ path, walkCompensatedPotential endpoint potential 0 path
    ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) ≤ _ at expectedMartingale
  simp only [walkCompensatedPotential, Finset.range_zero, Finset.sum_empty,
    sub_self, sub_zero, integral_zero] at expectedMartingale
  have initialIntegrable := (finitePathPotential_memLp_completion
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential 0 1).integrable le_rfl
  have martingaleIntegrable := martingale.submartingale.integrable_stoppedValue stopping bounded
  have potentialIntegrable := integrable_stoppedValue ℕ stopping
    (fun index => (finitePathPotential_memLp_completion
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential index 1).integrable le_rfl) bounded
  have pointwise (path : ℕ → Vertex) :
      potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path -
        time * driftBound ≤ stoppedValue (fun index path => potential (path index)) stoppingTime path := by
    have finite : stoppingTime path ≠ ⊤ := by
      intro equality
      have contradiction := bounded path
      simp [equality] at contradiction
    have countBound : (stoppingTime path).untopA ≤ time := by
      lift stoppingTime path to ℕ using finite with count equality
      have bound := bounded path
      rw [← equality] at bound
      change count ≤ time
      exact WithTop.coe_le_coe.mp bound
    have driftLower : -(time * driftBound) ≤
        ∑ index ∈ Finset.range (stoppingTime path).untopA,
          rateOneGenerator endpoint potential (path index) := by
      calc
        _ ≤ -((stoppingTime path).untopA * driftBound) := by
          have countReal : ((stoppingTime path).untopA : ℝ) ≤ time := by exact_mod_cast countBound
          exact neg_le_neg (mul_le_mul_of_nonneg_right countReal driftNonnegative)
        _ = ∑ _index ∈ Finset.range (stoppingTime path).untopA, -driftBound := by simp
        _ ≤ _ := Finset.sum_le_sum fun index _ => (abs_le.mp (generatorBound (path index))).1
    dsimp [stoppedValue, walkCompensatedPotential]
    linarith
  have comparison := integral_mono
    ((initialIntegrable.add martingaleIntegrable).sub (integrable_const (time * driftBound)))
    potentialIntegrable pointwise
  have split :
      (∫ path, potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path -
        time * driftBound ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      (∫ path, stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) - time * driftBound := by
    have differenceSplit :
        (∫ path, potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path -
          time * driftBound ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
        (∫ path, potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path
          ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) -
        ∫ _path, time * driftBound ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
      integral_sub (initialIntegrable.add martingaleIntegrable) (integrable_const _)
    rw [differenceSplit]
    have sumSplit :
        (∫ path, potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path
          ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
        (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
        ∫ path, stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path
          ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := integral_add initialIntegrable martingaleIntegrable
    rw [sumSplit]
    simp
  change (∫ path, potential (path 0) + stoppedValue (walkCompensatedPotential endpoint potential) stoppingTime path -
    time * driftBound ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) ≤ _ at comparison
  rw [split] at comparison
  linarith

/-- Uniform bounded-time exit control uses a local separating potential.
It applies to any starting distribution and does not use stationarity. -/
theorem finiteDiscreteWalkLaw_exit_bound_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (potentialUpper : ∀ vertex, potential vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (threshold : ℝ) (thresholdBelowOne : threshold < 1) (time : ℕ) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      {path | ∃ index ≤ time, potential (path index) ≤ threshold} ≤
        1 - (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
          time * driftBound := by
  let process : ℕ → (ℕ → Vertex) → ℝ := fun index path => potential (path index)
  let stoppingTime : (ℕ → Vertex) → WithTop ℕ :=
    fun path => ((hittingBtwn process (Set.Iic threshold) 0 time path : ℕ) : WithTop ℕ)
  have adapted : StronglyAdapted Filtration.piLE process :=
    fun index => finitePathPotential_stronglyMeasurable_past_completion potential index index le_rfl
  have stopping : IsStoppingTime Filtration.piLE stoppingTime :=
    adapted.adapted.isStoppingTime_hittingBtwn (n := 0) (n' := time) measurableSet_Iic
  have bounded : ∀ path, stoppingTime path ≤ time := fun path => by
    change ((hittingBtwn process (Set.Iic threshold) 0 time path : ℕ) : WithTop ℕ) ≤ (time : WithTop ℕ)
    exact_mod_cast hittingBtwn_le (u := process) (s := Set.Iic threshold) (n := 0) (m := time) path
  have lower := finiteDiscreteWalkLaw_stopped_potential_lower_completion endpoint positiveDegree
    initial potential driftBound driftNonnegative generatorBound stoppingTime stopping time bounded
  have stoppedIntegrable := integrable_stoppedValue ℕ stopping
    (fun index => (finitePathPotential_memLp_completion
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential index 1).integrable le_rfl) bounded
  have deficitIntegrable := (integrable_const (1 : ℝ)).sub stoppedIntegrable
  have eventMeasurable : MeasurableSet {path : ℕ → Vertex | ∃ index ≤ time, potential (path index) ≤ threshold} := by
    convert (MeasurableSet.iUnion fun (index : ℕ) => MeasurableSet.iUnion fun (_ : index ≤ time) =>
      measurableSet_le ((measurable_of_countable potential).comp (measurable_pi_apply index))
        (measurable_const (a := threshold))) using 1
    ext path
    simp
  have hitBound : ∀ path ∈ {path : ℕ → Vertex | ∃ index ≤ time, potential (path index) ≤ threshold},
      1 - threshold ≤ 1 - stoppedValue process stoppingTime path := by
    intro path witness
    obtain ⟨index, indexBound, hit⟩ := witness
    have stoppedHit := hittingBtwn_mem_set (u := process) (s := Set.Iic threshold) (n := 0) (m := time)
      (ω := path) ⟨index, ⟨Nat.zero_le index, indexBound⟩, hit⟩
    change process (hittingBtwn process (Set.Iic threshold) 0 time path) path ≤ threshold at stoppedHit
    change 1 - threshold ≤ 1 - process (hittingBtwn process (Set.Iic threshold) 0 time path) path
    linarith
  have integralHit := setIntegral_ge_of_const_le_real eventMeasurable
    (measure_ne_top _ _) hitBound deficitIntegrable.integrableOn
  have fullBound := setIntegral_le_integral
    (s := {path : ℕ → Vertex | ∃ index ≤ time, potential (path index) ≤ threshold}) deficitIntegrable
    (Eventually.of_forall fun path => by
      change 0 ≤ 1 - potential (path (stoppingTime path).untopA)
      linarith [potentialUpper (path (stoppingTime path).untopA)])
  have split : (∫ path, 1 - stoppedValue process stoppingTime path
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      1 - ∫ path, stoppedValue process stoppingTime path
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
    rw [integral_sub (integrable_const _) stoppedIntegrable]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  change (∫ path in {path : ℕ → Vertex | ∃ index ≤ time, potential (path index) ≤ threshold},
    1 - stoppedValue process stoppingTime path ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) ≤
    ∫ path, 1 - stoppedValue process stoppingTime path
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial at fullBound
  rw [split] at fullBound
  change (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real _ ≤ _ at integralHit
  linarith

end
end IGSIII34.Diffusion
