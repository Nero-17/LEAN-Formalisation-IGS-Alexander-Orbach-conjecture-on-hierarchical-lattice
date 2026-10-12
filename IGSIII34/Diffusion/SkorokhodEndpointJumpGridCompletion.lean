import IGSIII34.Diffusion.IntervalFiniteKnotsCompletion
import IGSIII34.Diffusion.SkorokhodRegularGridCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space]

def finiteEndpointJumpIntervalPathCompletion {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count+1) → Space) (endpoint : Space) : SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => if time.val = 1 then endpoint else finiteJumpIntervalPathCompletion knots states time⟩

def roundedIntervalKnotCompletion (grid : ℕ) (time : SkorokhodIntervalTimeCompletion) :
    SkorokhodIntervalTimeCompletion :=
  ⟨(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ), by
    have positive : 0 < (grid+1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) positive.le
    · apply (div_le_one positive).mpr
      have bound : ⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ ≤ grid+1 := Nat.ceil_le.mpr (by
        simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
          mul_le_mul_of_nonneg_left time.property.2 positive.le)
      exact_mod_cast bound⟩

theorem roundedIntervalKnot_distance_completion (grid : ℕ)
    (time : SkorokhodIntervalTimeCompletion) :
    dist (roundedIntervalKnotCompletion grid time) time ≤ 1 / (grid+1 : ℝ) := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  have lower := Nat.le_ceil ((grid+1 : ℝ) * (time : ℝ))
  have upper := Nat.ceil_lt_add_one (mul_nonneg positive.le time.property.1)
  change |(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) - (time : ℝ)| ≤ _
  have quotientLower : (time : ℝ) ≤ (⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) :=
    (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using lower)
  rw [abs_of_nonneg (sub_nonneg.mpr quotientLower)]
  apply (le_div_iff₀ positive).mpr
  rw [sub_mul, div_mul_cancel₀ _ positive.ne']
  nlinarith

theorem roundedIntervalKnot_tendsto_completion
    (time : SkorokhodIntervalTimeCompletion) :
    Tendsto (fun grid => roundedIntervalKnotCompletion grid time) atTop (𝓝 time) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [skorokhodRegularGrid_mesh_tendsto_completion.eventually (gt_mem_nhds positive)] with grid small
  exact (roundedIntervalKnot_distance_completion grid time).trans_lt small

theorem roundedIntervalKnot_grid_inequality_completion (grid : ℕ)
    (knot time : SkorokhodIntervalTimeCompletion) :
    knot ≤ skorokhodRegularGridPointCompletion grid (skorokhodRegularGridSelectionCompletion grid time) ↔
      roundedIntervalKnotCompletion grid knot ≤ time := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  change (knot : ℝ) ≤ (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ↔
    (⌈(grid+1 : ℝ) * (knot : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
  rw [le_div_iff₀ positive, div_le_iff₀ positive]
  rw [mul_comm (knot : ℝ), ← Nat.ceil_le,
    mul_comm (time : ℝ), ← Nat.le_floor_iff (mul_nonneg positive.le time.property.1)]

theorem finiteEndpointJump_grid_identity_completion {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count+1) → Space) (endpoint : Space) (grid : ℕ) :
    skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid)
      (fun index => finiteEndpointJumpIntervalPathCompletion knots states endpoint
        (skorokhodRegularGridPointCompletion grid index)) =
      finiteEndpointJumpIntervalPathCompletion (fun index => roundedIntervalKnotCompletion grid (knots index)) states endpoint := by
  classical
  apply congrArg SkorokhodIntervalPathCompletion.mk
  funext time
  by_cases terminal : time.val = 1
  · have gridTerminal : (skorokhodRegularGridPointCompletion grid
        (skorokhodRegularGridSelectionCompletion grid time)).val = 1 := by
      change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) = 1
      rw [terminal, mul_one]
      have floorIdentity : ⌊(grid+1 : ℝ)⌋₊ = grid+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (grid+1)
      rw [floorIdentity]
      push_cast
      exact div_self (by positivity)
    simp only [skorokhodFiniteReconstructionCompletion,
      finiteEndpointJumpIntervalPathCompletion, terminal, gridTerminal, if_true]
  · have gridNotTerminal : (skorokhodRegularGridPointCompletion grid
        (skorokhodRegularGridSelectionCompletion grid time)).val ≠ 1 := by
      have bound := Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (grid+1 : ℝ)) time.property.1)
      have quotientBound : (skorokhodRegularGridPointCompletion grid
          (skorokhodRegularGridSelectionCompletion grid time)).val ≤ time.val := by
        change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
        apply (div_le_iff₀ (by positivity : 0 < (grid+1 : ℝ))).mpr
        simpa only [mul_comm] using bound
      exact ne_of_lt (quotientBound.trans_lt (lt_of_le_of_ne time.property.2 terminal))
    simp only [skorokhodFiniteReconstructionCompletion,
      finiteEndpointJumpIntervalPathCompletion, terminal, gridNotTerminal, if_false]
    change states _ = states _
    congr 1
    apply Fin.ext
    unfold finiteJumpCountCompletion
    change (Finset.univ.filter (fun index => knots index ≤ skorokhodRegularGridPointCompletion grid
      (skorokhodRegularGridSelectionCompletion grid time))).card =
        (Finset.univ.filter (fun index => roundedIntervalKnotCompletion grid (knots index) ≤ time)).card
    apply congrArg Finset.card
    apply Finset.ext
    intro index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact roundedIntervalKnot_grid_inequality_completion grid (knots index) time

theorem finiteEndpointJump_time_change_completion {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion)
    (states : Fin (count+1) → Space) (endpoint : Space)
    (change : SkorokhodIntervalTimeCompletion ≃o SkorokhodIntervalTimeCompletion)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion) :
    finiteEndpointJumpIntervalPathCompletion second states endpoint (change time) =
      finiteEndpointJumpIntervalPathCompletion first states endpoint time := by
  have endpointEquivalent : (change time).val = 1 ↔ time.val = 1 := by
    have identity := intervalOrderIso_one_fixed_completion change
    constructor
    · intro equal
      have typed : change time = (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion) := Subtype.ext equal
      rw [← identity] at typed
      exact congrArg Subtype.val (change.injective typed)
    · intro equal
      have typed : time = (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion) := Subtype.ext equal
      rw [typed, identity]
  simp only [finiteEndpointJumpIntervalPathCompletion, endpointEquivalent]
  split_ifs
  · rfl
  · exact finiteJumpIntervalPath_time_change_completion first second states change knotIdentity time

theorem finiteEndpointJump_grid_tendsto_completion [CompactSpace Space] {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion) (increasing : StrictMono knots)
    (interior : ∀ index, 0 < (knots index).val ∧ (knots index).val < 1)
    (states : Fin (count+1) → Space) (endpoint : Space) :
    Tendsto (fun grid => skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid)
      (fun index => finiteEndpointJumpIntervalPathCompletion knots states endpoint
        (skorokhodRegularGridPointCompletion grid index))) atTop
      (𝓝 (finiteEndpointJumpIntervalPathCompletion knots states endpoint)) := by
  have increasingEventually : ∀ᶠ grid : ℕ in atTop, StrictMono (fun index => roundedIntervalKnotCompletion grid (knots index)) := by
    have pairs : ∀ first second : Fin count, ∀ᶠ grid : ℕ in atTop,
        first < second → roundedIntervalKnotCompletion grid (knots first) < roundedIntervalKnotCompletion grid (knots second) := by
      intro first second
      by_cases before : first < second
      · exact ((roundedIntervalKnot_tendsto_completion (knots first)).eventually_lt
          (roundedIntervalKnot_tendsto_completion (knots second)) (increasing before)).mono (fun _ bound _ => bound)
      · exact Eventually.of_forall (fun _ impossible => (before impossible).elim)
    exact (Filter.eventually_all.mpr (fun first => Filter.eventually_all.mpr (pairs first))).mono (fun _ pairBound => pairBound)
  have interiorEventually : ∀ᶠ grid : ℕ in atTop, ∀ index,
      0 < (roundedIntervalKnotCompletion grid (knots index)).val ∧
      (roundedIntervalKnotCompletion grid (knots index)).val < 1 := by
    apply Filter.eventually_all.mpr
    intro index
    have convergence := continuous_subtype_val.tendsto (knots index) |>.comp (roundedIntervalKnot_tendsto_completion (knots index))
    exact (convergence.eventually (Ioo_mem_nhds (interior index).1 (interior index).2))
  have errorConvergence : Tendsto (fun grid : ℕ => ((2 : ℝ)^count-1) * (1/(grid+1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using skorokhodRegularGrid_mesh_tendsto_completion.const_mul ((2 : ℝ)^count-1)
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [increasingEventually, interiorEventually, errorConvergence.eventually (gt_mem_nhds positive)]
    with grid roundedIncreasing roundedInterior errorSmall
  obtain ⟨change, knotIdentity, displacement⟩ := interval_finite_knots_orderIso_completion count knots
    (fun index => roundedIntervalKnotCompletion grid (knots index)) increasing roundedIncreasing interior roundedInterior
    (1/(grid+1 : ℝ)) (fun index => by simpa only [dist_comm] using roundedIntervalKnot_distance_completion grid (knots index))
  have edistance : edist
      (finiteEndpointJumpIntervalPathCompletion (fun index => roundedIntervalKnotCompletion grid (knots index)) states endpoint)
      (finiteEndpointJumpIntervalPathCompletion knots states endpoint) ≤
      ENNReal.ofReal (((2 : ℝ)^count-1) * (1/(grid+1 : ℝ))) := by
    apply iInf_le_of_le change
    apply max_le
    · apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (displacement time)
    · apply iSup_le
      intro time
      rw [finiteEndpointJump_time_change_completion knots _ states endpoint change knotIdentity time, edist_self]
      exact zero_le
  rw [finiteEndpointJump_grid_identity_completion]
  apply edist_lt_ofReal.mp
  exact edistance.trans_lt ((ENNReal.ofReal_lt_ofReal_iff positive).mpr errorSmall)

end
end IGSIII34.Diffusion
