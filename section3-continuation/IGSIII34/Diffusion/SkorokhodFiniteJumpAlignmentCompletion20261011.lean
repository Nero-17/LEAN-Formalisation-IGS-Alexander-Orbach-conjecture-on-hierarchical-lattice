import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space]

def finiteJumpCountCompletion20261011 {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (time : SkorokhodIntervalTimeCompletion20261011) : ℕ := by
  classical
  exact (Finset.univ.filter (fun index => knots index ≤ time)).card

theorem finiteJumpCount_le_completion20261011 {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (time : SkorokhodIntervalTimeCompletion20261011) : finiteJumpCountCompletion20261011 knots time ≤ count := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin count)

def finiteJumpIntervalPathCompletion20261011 {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count + 1) → Space) : SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => states ⟨finiteJumpCountCompletion20261011 knots time,
    Nat.lt_succ_of_le (finiteJumpCount_le_completion20261011 knots time)⟩⟩

theorem finiteJumpCount_time_change_completion20261011 {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    finiteJumpCountCompletion20261011 second (change time) = finiteJumpCountCompletion20261011 first time := by
  classical
  unfold finiteJumpCountCompletion20261011
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← knotIdentity index, change.le_iff_le]

theorem finiteJumpIntervalPath_time_change_completion20261011 {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count + 1) → Space)
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    finiteJumpIntervalPathCompletion20261011 second states (change time) =
      finiteJumpIntervalPathCompletion20261011 first states time := by
  change states _ = states _
  congr 1
  apply Fin.ext
  exact finiteJumpCount_time_change_completion20261011 first second change knotIdentity time

/-- Matching the finitely many jump times by an actual interval order
isomorphism identifies every spatial value of the paths. -/
theorem finiteJumpIntervalPath_J1_bound_completion20261011 {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count + 1) → Space)
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (knotIdentity : ∀ index, change (first index) = second index)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (timeBound : ∀ time, dist (change time) time ≤ error) :
    edist (finiteJumpIntervalPathCompletion20261011 second states)
      (finiteJumpIntervalPathCompletion20261011 first states) ≤ ENNReal.ofReal error := by
  change skorokhodJ1EDistCompletion20261011 _ _ ≤ _
  apply iInf_le_of_le change
  apply max_le
  · apply iSup_le
    intro time
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (timeBound time)
  · apply iSup_le
    intro time
    rw [finiteJumpIntervalPath_time_change_completion20261011 first second states change knotIdentity, edist_self]
    exact zero_le

end
end IGSIII34.Diffusion

