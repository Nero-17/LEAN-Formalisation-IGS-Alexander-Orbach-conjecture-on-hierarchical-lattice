import IGSIII34.Diffusion.ConditionalWindowExitCompletion

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

def finitePotentialWindowHitCompletion (potential : Vertex → ℝ) (threshold : ℝ)
    (first : (ℕ → Vertex) → WithTop ℕ) (horizon window : ℕ) (path : ℕ → Vertex) : WithTop ℕ :=
  min ((hittingBtwn (fun index path => potential (path index)) (Set.Iic threshold)
    (first path).untopA (horizon + window) path : ℕ) : WithTop ℕ) (first path + window)

theorem finitePotentialWindowHit_properties_completion
    (potential : Vertex → ℝ) (threshold : ℝ)
    (first : (ℕ → Vertex) → WithTop ℕ) (firstStopping : IsStoppingTime Filtration.piLE first)
    (horizon window : ℕ) (bounded : ∀ path, first path ≤ horizon) :
    IsStoppingTime Filtration.piLE (finitePotentialWindowHitCompletion potential threshold first horizon window) ∧
    first ≤ finitePotentialWindowHitCompletion potential threshold first horizon window ∧
    (∀ path, finitePotentialWindowHitCompletion potential threshold first horizon window path ≤ horizon + window) ∧
    (∀ path, (finitePotentialWindowHitCompletion potential threshold first horizon window path).untopA ≤
      (first path).untopA + window) ∧
    (∀ path, (∃ index, (first path).untopA ≤ index ∧ index ≤ (first path).untopA + window ∧
      potential (path index) ≤ threshold) →
      potential (path (finitePotentialWindowHitCompletion potential threshold first horizon window path).untopA) ≤ threshold) := by
  let process : ℕ → (ℕ → Vertex) → ℝ := fun index path => potential (path index)
  have adapted : StronglyAdapted Filtration.piLE process :=
    fun index => finitePathPotential_stronglyMeasurable_past_completion potential index index le_rfl
  have boundedLong : ∀ path, first path ≤ horizon + window := fun path =>
    (bounded path).trans (WithTop.coe_le_coe.mpr (Nat.le_add_right horizon window))
  have stoppingHit := Adapted.isStoppingTime_hittingBtwn_isStoppingTime (s := Set.Iic threshold)
    (N := horizon + window) firstStopping boundedLong
    measurableSet_Iic adapted.adapted
  have stopping := stoppingHit.min (firstStopping.add_const' window)
  have firstFinite (path : ℕ → Vertex) : first path ≠ ⊤ := by
    intro equality
    have contradiction := bounded path
    simp [equality] at contradiction
  have firstCount (path : ℕ → Vertex) : (first path).untopA ≤ horizon :=
    (WithTop.untopA_le_iff (firstFinite path)).mpr (bounded path)
  have countIdentity (path : ℕ → Vertex) : ((first path).untopA : WithTop ℕ) = first path := by
    lift first path to ℕ using firstFinite path with count equality
    rfl
  refine ⟨stopping, ?_, ?_, ?_, ?_⟩
  · intro path
    apply le_min
    · rw [← countIdentity path]
      exact WithTop.coe_le_coe.mpr (le_hittingBtwn
        ((firstCount path).trans (Nat.le_add_right horizon window)) path)
    · rw [← countIdentity path]
      exact WithTop.coe_le_coe.mpr (Nat.le_add_right _ _)
  · intro path
    apply (min_le_left _ _).trans
    exact WithTop.coe_le_coe.mpr (hittingBtwn_le (u := process) (s := Set.Iic threshold)
      (n := (first path).untopA) (m := horizon + window) path)
  · intro path
    have finite : finitePotentialWindowHitCompletion potential threshold first horizon window path ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    apply (WithTop.untopA_le_iff finite).mpr
    change min _ (first path + window) ≤ _
    rw [← countIdentity path]
    exact min_le_right _ _
  · intro path hit
    obtain ⟨index, after, before, hit⟩ := hit
    have indexHorizon : index ≤ horizon + window := by linarith [firstCount path]
    have hitEarly := hittingBtwn_le_of_mem (u := process) (s := Set.Iic threshold)
      (n := (first path).untopA) (m := horizon + window) after indexHorizon hit
    have hitWithin : hittingBtwn process (Set.Iic threshold) (first path).untopA (horizon + window) path ≤
        (first path).untopA + window := hitEarly.trans before
    have hitMember := hittingBtwn_mem_set (u := process) (s := Set.Iic threshold)
      (n := (first path).untopA) (m := horizon + window) (ω := path) ⟨index, ⟨after, indexHorizon⟩, hit⟩
    change potential (path (min ((hittingBtwn process (Set.Iic threshold) (first path).untopA
      (horizon + window) path : ℕ) : WithTop ℕ) (first path + window)).untopA) ≤ threshold
    rw [min_eq_left (by
      rw [← countIdentity path]
      exact WithTop.coe_le_coe.mpr hitWithin)]
    exact hitMember

theorem finitePotentialWindowHit_event_measurable_completion
    (potential : Vertex → ℝ) (threshold : ℝ)
    (first : (ℕ → Vertex) → WithTop ℕ) (firstStopping : IsStoppingTime Filtration.piLE first)
    (horizon window : ℕ) (bounded : ∀ path, first path ≤ horizon) :
    MeasurableSet {path | ∃ index, (first path).untopA ≤ index ∧
      index ≤ (first path).untopA + window ∧ potential (path index) ≤ threshold} := by
  have finite (path : ℕ → Vertex) : first path ≠ ⊤ := by
    intro equality
    have contradiction := bounded path
    simp [equality] at contradiction
  have identity : {path | ∃ index, (first path).untopA ≤ index ∧
      index ≤ (first path).untopA + window ∧ potential (path index) ≤ threshold} =
      ⋃ start : ℕ, ⋃ index : ℕ, ⋃ (_ : start ≤ index), ⋃ (_ : index ≤ start + window),
        {path | first path = (start : WithTop ℕ)} ∩ {path | potential (path index) ≤ threshold} := by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨index, after, before, hit⟩
      refine ⟨(first path).untopA, index, after, before, ?_, hit⟩
      lift first path to ℕ using finite path with count equality
      rfl
    · rintro ⟨start, index, after, before, equal, hit⟩
      refine ⟨index, ?_, ?_, hit⟩ <;> simpa only [equal] using (by assumption)
  rw [identity]
  exact MeasurableSet.iUnion fun start => MeasurableSet.iUnion fun index =>
    MeasurableSet.iUnion fun _after => MeasurableSet.iUnion fun _before =>
      (firstStopping.measurableSpace_le _ (firstStopping.measurableSet_eq' start)).inter
        (measurableSet_le ((measurable_of_countable potential).comp (measurable_pi_apply index)) measurable_const)

/-- A real first exit in a stopped window satisfies the conditional
duration-only bound. Its stopping time and event measurability are proved
here from the walk coordinates. -/
theorem finiteDiscreteWalkLaw_first_exit_window_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (potentialUpper : ∀ vertex, potential vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (first : (ℕ → Vertex) → WithTop ℕ) (firstStopping : IsStoppingTime Filtration.piLE first)
    (horizon window : ℕ) (bounded : ∀ path, first path ≤ horizon)
    (event : Set (ℕ → Vertex)) (known : MeasurableSet[firstStopping.measurableSpace] event)
    (error threshold : ℝ) (startBound : ∀ path ∈ event, 1 - error ≤ potential (path (first path).untopA)) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      (event ∩ {path | ∃ index, (first path).untopA ≤ index ∧ index ≤ (first path).untopA + window ∧
        potential (path index) ≤ threshold}) ≤
      (error + window * driftBound) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real event := by
  obtain ⟨stopping, ordered, boundedHit, lengthBound, hitBound⟩ :=
    finitePotentialWindowHit_properties_completion potential threshold first firstStopping horizon window bounded
  exact finiteDiscreteWalkLaw_conditional_exit_completion endpoint positiveDegree initial potential
    potentialUpper driftBound driftNonnegative generatorBound first
    (finitePotentialWindowHitCompletion potential threshold first horizon window)
    firstStopping stopping ordered (horizon + window) window boundedHit lengthBound event known error threshold startBound
    _ (finitePotentialWindowHit_event_measurable_completion potential threshold first firstStopping horizon window bounded)
    hitBound

end
end IGSIII34.Diffusion
