import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space]

def finiteJumpCountCompletion {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion)
    (time : SkorokhodIntervalTimeCompletion) : ℕ := by
  classical
  exact (Finset.univ.filter (fun index => knots index ≤ time)).card

theorem finiteJumpCount_le_completion {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion)
    (time : SkorokhodIntervalTimeCompletion) : finiteJumpCountCompletion knots time ≤ count := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin count)

def finiteJumpIntervalPathCompletion {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count + 1) → Space) : SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => states ⟨finiteJumpCountCompletion knots time,
    Nat.lt_succ_of_le (finiteJumpCount_le_completion knots time)⟩⟩

theorem finiteJumpCount_time_change_completion {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion)
    (change : SkorokhodIntervalTimeCompletion ≃o SkorokhodIntervalTimeCompletion)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion) :
    finiteJumpCountCompletion second (change time) = finiteJumpCountCompletion first time := by
  classical
  unfold finiteJumpCountCompletion
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← knotIdentity index, change.le_iff_le]

theorem finiteJumpIntervalPath_time_change_completion {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count + 1) → Space)
    (change : SkorokhodIntervalTimeCompletion ≃o SkorokhodIntervalTimeCompletion)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion) :
    finiteJumpIntervalPathCompletion second states (change time) =
      finiteJumpIntervalPathCompletion first states time := by
  change states _ = states _
  congr 1
  apply Fin.ext
  exact finiteJumpCount_time_change_completion first second change knotIdentity time

/-- Matching the finitely many jump times by an actual interval order
isomorphism identifies every spatial value of the paths. -/
theorem finiteJumpIntervalPath_J1_bound_completion {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count + 1) → Space)
    (change : SkorokhodIntervalTimeCompletion ≃o SkorokhodIntervalTimeCompletion)
    (knotIdentity : ∀ index, change (first index) = second index)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (timeBound : ∀ time, dist (change time) time ≤ error) :
    edist (finiteJumpIntervalPathCompletion second states)
      (finiteJumpIntervalPathCompletion first states) ≤ ENNReal.ofReal error := by
  change skorokhodJ1EDistCompletion _ _ ≤ _
  apply iInf_le_of_le change
  apply max_le
  · apply iSup_le
    intro time
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (timeBound time)
  · apply iSup_le
    intro time
    rw [finiteJumpIntervalPath_time_change_completion first second states change knotIdentity, edist_self]
    exact zero_le

end
end IGSIII34.Diffusion

