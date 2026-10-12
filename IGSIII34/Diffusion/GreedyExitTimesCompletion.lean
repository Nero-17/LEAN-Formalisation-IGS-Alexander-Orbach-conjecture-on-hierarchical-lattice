import IGSIII34.Diffusion.FiniteResolventStoppingCoverCompletion

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Vertex Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [MetricSpace Carrier]

def finiteGreedyExitNextCompletion (embedding : Vertex → Carrier) (radius : ℝ)
    (horizon : ℕ) (first : (ℕ → Vertex) → ℕ) (path : ℕ → Vertex) : ℕ :=
  hittingBtwn (fun index path => dist (embedding (path (first path))) (embedding (path index)))
    (Set.Ici radius) (first path) (horizon + 1) path

def finiteGreedyExitTimeCompletion (embedding : Vertex → Carrier) (radius : ℝ)
    (horizon : ℕ) : ℕ → (ℕ → Vertex) → ℕ
  | 0 => fun _ => 0
  | step + 1 => finiteGreedyExitNextCompletion embedding radius horizon
      (finiteGreedyExitTimeCompletion embedding radius horizon step)

theorem finiteGreedyExitNext_bound_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon : ℕ)
    (first : (ℕ → Vertex) → ℕ) (bounded : ∀ path, first path ≤ horizon + 1)
    (path : ℕ → Vertex) :
    first path ≤ finiteGreedyExitNextCompletion embedding radius horizon first path ∧
      finiteGreedyExitNextCompletion embedding radius horizon first path ≤ horizon + 1 :=
  ⟨le_hittingBtwn (bounded path) path, hittingBtwn_le path⟩

theorem finiteGreedyExitNext_le_iff_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon : ℕ)
    (first : (ℕ → Vertex) → ℕ) (path : ℕ → Vertex)
    (index : ℕ) (before : index ≤ horizon) :
    finiteGreedyExitNextCompletion embedding radius horizon first path ≤ index ↔
      ∃ hit, first path ≤ hit ∧ hit ≤ index ∧
        radius ≤ dist (embedding (path (first path))) (embedding (path hit)) := by
  simpa only [finiteGreedyExitNextCompletion, Set.mem_Icc, Set.mem_Ici, and_assoc] using
    (hittingBtwn_le_iff_of_lt
      (u := fun index path => dist (embedding (path (first path))) (embedding (path index)))
      (s := Set.Ici radius) (n := first path) (m := horizon + 1) (ω := path) index (by omega))

theorem finiteGreedyExitNext_before_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon : ℕ)
    (first : (ℕ → Vertex) → ℕ) (path : ℕ → Vertex)
    (index : ℕ) (after : first path ≤ index)
    (before : index < finiteGreedyExitNextCompletion embedding radius horizon first path) :
    dist (embedding (path (first path))) (embedding (path index)) < radius := by
  exact not_le.mp (notMem_of_lt_hittingBtwn
    (u := fun index path => dist (embedding (path (first path))) (embedding (path index)))
    (s := Set.Ici radius) (n := first path) (m := horizon + 1) (ω := path) before after)

theorem finiteGreedyExitNext_hit_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon : ℕ)
    (first : (ℕ → Vertex) → ℕ) (path : ℕ → Vertex)
    (actualExit : finiteGreedyExitNextCompletion embedding radius horizon first path ≤ horizon) :
    radius ≤ dist (embedding (path (first path)))
      (embedding (path (finiteGreedyExitNextCompletion embedding radius horizon first path))) :=
  hittingBtwn_mem_set_of_hittingBtwn_lt
    (u := fun index path => dist (embedding (path (first path))) (embedding (path index)))
    (s := Set.Ici radius) (n := first path) (m := horizon + 1) (ω := path) (by
      change finiteGreedyExitNextCompletion embedding radius horizon first path < horizon + 1
      omega)

theorem finiteMetricPair_measurable_past_completion
    (embedding : Vertex → Carrier) (first last time : ℕ)
    (firstBefore : first ≤ time) (lastBefore : last ≤ time) :
    Measurable[Filtration.piLE time] (fun path : ℕ → Vertex =>
      dist (embedding (path first)) (embedding (path last))) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have firstObservable : Measurable (fun history : (coordinate : Finset.Iic time) → Vertex =>
      history ⟨first, Finset.mem_Iic.mpr firstBefore⟩) := measurable_pi_apply _
  have lastObservable : Measurable (fun history : (coordinate : Finset.Iic time) → Vertex =>
      history ⟨last, Finset.mem_Iic.mpr lastBefore⟩) := measurable_pi_apply _
  have observable : Measurable (fun history : (coordinate : Finset.Iic time) → Vertex =>
      dist (embedding (history ⟨first, Finset.mem_Iic.mpr firstBefore⟩))
        (embedding (history ⟨last, Finset.mem_Iic.mpr lastBefore⟩))) := by
    exact (measurable_of_countable (fun pair : Vertex × Vertex => dist (embedding pair.1) (embedding pair.2))).comp
      (firstObservable.prodMk lastObservable)
  exact observable.comp (Measurable.of_comap_le le_rfl)

theorem finiteGreedyExitNext_stopping_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon : ℕ)
    (first : (ℕ → Vertex) → ℕ)
    (stopping : IsStoppingTime Filtration.piLE (fun path => (first path : WithTop ℕ)))
    (bounded : ∀ path, first path ≤ horizon + 1) :
    IsStoppingTime Filtration.piLE (fun path =>
      (finiteGreedyExitNextCompletion embedding radius horizon first path : WithTop ℕ)) := by
  intro time
  change MeasurableSet[Filtration.piLE time] {path : ℕ → Vertex |
    (finiteGreedyExitNextCompletion embedding radius horizon first path : WithTop ℕ) ≤ time}
  by_cases beyond : horizon + 1 ≤ time
  · have identity : {path : ℕ → Vertex |
        (finiteGreedyExitNextCompletion embedding radius horizon first path : WithTop ℕ) ≤ time} = Set.univ := by
      ext path
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact_mod_cast (finiteGreedyExitNext_bound_completion embedding radius horizon first bounded path).2.trans beyond
    rw [identity]
    exact MeasurableSet.univ
  · have before : time ≤ horizon := by omega
    have identity : {path : ℕ → Vertex |
        (finiteGreedyExitNextCompletion embedding radius horizon first path : WithTop ℕ) ≤ time} =
        ⋃ start : ℕ, ⋃ hit : ℕ, ⋃ (_ : start ≤ hit), ⋃ (_ : hit ≤ time),
          {path | (first path : WithTop ℕ) = start} ∩
            {path | radius ≤ dist (embedding (path start)) (embedding (path hit))} := by
      ext path
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
      norm_cast
      rw [finiteGreedyExitNext_le_iff_completion embedding radius horizon first path time before]
      constructor
      · rintro ⟨hit, after, before, far⟩
        exact ⟨first path, hit, after, before, rfl, far⟩
      · rintro ⟨start, hit, after, before, equality, far⟩
        exact ⟨hit, equality ▸ after, before, equality ▸ far⟩
    rw [identity]
    exact MeasurableSet.iUnion fun start => MeasurableSet.iUnion fun hit =>
      MeasurableSet.iUnion fun after => MeasurableSet.iUnion fun before =>
        (stopping.measurableSet_eq_le (after.trans before)).inter
          (measurableSet_le measurable_const
            (finiteMetricPair_measurable_past_completion embedding start hit time (after.trans before) before))

theorem finiteGreedyExitTime_properties_completion
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon step : ℕ) :
    IsStoppingTime Filtration.piLE (fun path =>
      (finiteGreedyExitTimeCompletion embedding radius horizon step path : WithTop ℕ)) ∧
      (∀ path, finiteGreedyExitTimeCompletion embedding radius horizon step path ≤ horizon + 1) ∧
      (∀ path, finiteGreedyExitTimeCompletion embedding radius horizon step path ≤
        finiteGreedyExitTimeCompletion embedding radius horizon (step + 1) path) := by
  induction step with
  | zero =>
    refine ⟨isStoppingTime_const Filtration.piLE 0, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | succ step induction =>
    have nextStopping := finiteGreedyExitNext_stopping_completion embedding radius horizon
      (finiteGreedyExitTimeCompletion embedding radius horizon step) induction.1 induction.2.1
    have nextBounded : ∀ path, finiteGreedyExitTimeCompletion embedding radius horizon (step + 1) path ≤ horizon + 1 :=
      fun path => (finiteGreedyExitNext_bound_completion embedding radius horizon _ induction.2.1 path).2
    exact ⟨nextStopping, nextBounded,
      fun path => (finiteGreedyExitNext_bound_completion embedding radius horizon _ nextBounded path).1⟩

end
end IGSIII34.Diffusion
