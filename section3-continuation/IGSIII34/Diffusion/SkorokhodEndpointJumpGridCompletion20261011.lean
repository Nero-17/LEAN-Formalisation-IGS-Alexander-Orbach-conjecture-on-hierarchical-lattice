import IGSIII34.Diffusion.IntervalFiniteKnotsCompletion20261011
import IGSIII34.Diffusion.SkorokhodRegularGridCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space]

def finiteEndpointJumpIntervalPathCompletion20261011 {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count+1) → Space) (endpoint : Space) : SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => if time.val = 1 then endpoint else finiteJumpIntervalPathCompletion20261011 knots states time⟩

def roundedIntervalKnotCompletion20261011 (grid : ℕ) (time : SkorokhodIntervalTimeCompletion20261011) :
    SkorokhodIntervalTimeCompletion20261011 :=
  ⟨(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ), by
    have positive : 0 < (grid+1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) positive.le
    · apply (div_le_one positive).mpr
      have bound : ⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ ≤ grid+1 := Nat.ceil_le.mpr (by
        simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
          mul_le_mul_of_nonneg_left time.property.2 positive.le)
      exact_mod_cast bound⟩

theorem roundedIntervalKnot_distance_completion20261011 (grid : ℕ)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    dist (roundedIntervalKnotCompletion20261011 grid time) time ≤ 1 / (grid+1 : ℝ) := by
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

theorem roundedIntervalKnot_tendsto_completion20261011
    (time : SkorokhodIntervalTimeCompletion20261011) :
    Tendsto (fun grid => roundedIntervalKnotCompletion20261011 grid time) atTop (𝓝 time) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [skorokhodRegularGrid_mesh_tendsto_completion20261011.eventually (gt_mem_nhds positive)] with grid small
  exact (roundedIntervalKnot_distance_completion20261011 grid time).trans_lt small

theorem roundedIntervalKnot_grid_inequality_completion20261011 (grid : ℕ)
    (knot time : SkorokhodIntervalTimeCompletion20261011) :
    knot ≤ skorokhodRegularGridPointCompletion20261011 grid (skorokhodRegularGridSelectionCompletion20261011 grid time) ↔
      roundedIntervalKnotCompletion20261011 grid knot ≤ time := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  change (knot : ℝ) ≤ (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ↔
    (⌈(grid+1 : ℝ) * (knot : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
  rw [le_div_iff₀ positive, div_le_iff₀ positive]
  rw [mul_comm (knot : ℝ), ← Nat.ceil_le,
    mul_comm (time : ℝ), ← Nat.le_floor_iff (mul_nonneg positive.le time.property.1)]

theorem finiteEndpointJump_grid_identity_completion20261011 {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count+1) → Space) (endpoint : Space) (grid : ℕ) :
    skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid)
      (fun index => finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint
        (skorokhodRegularGridPointCompletion20261011 grid index)) =
      finiteEndpointJumpIntervalPathCompletion20261011 (fun index => roundedIntervalKnotCompletion20261011 grid (knots index)) states endpoint := by
  classical
  apply congrArg SkorokhodIntervalPathCompletion20261011.mk
  funext time
  by_cases terminal : time.val = 1
  · have gridTerminal : (skorokhodRegularGridPointCompletion20261011 grid
        (skorokhodRegularGridSelectionCompletion20261011 grid time)).val = 1 := by
      change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) = 1
      rw [terminal, mul_one]
      have floorIdentity : ⌊(grid+1 : ℝ)⌋₊ = grid+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (grid+1)
      rw [floorIdentity]
      push_cast
      exact div_self (by positivity)
    simp only [skorokhodFiniteReconstructionCompletion20261011,
      finiteEndpointJumpIntervalPathCompletion20261011, terminal, gridTerminal, if_true]
  · have gridNotTerminal : (skorokhodRegularGridPointCompletion20261011 grid
        (skorokhodRegularGridSelectionCompletion20261011 grid time)).val ≠ 1 := by
      have bound := Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (grid+1 : ℝ)) time.property.1)
      have quotientBound : (skorokhodRegularGridPointCompletion20261011 grid
          (skorokhodRegularGridSelectionCompletion20261011 grid time)).val ≤ time.val := by
        change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
        apply (div_le_iff₀ (by positivity : 0 < (grid+1 : ℝ))).mpr
        simpa only [mul_comm] using bound
      exact ne_of_lt (quotientBound.trans_lt (lt_of_le_of_ne time.property.2 terminal))
    simp only [skorokhodFiniteReconstructionCompletion20261011,
      finiteEndpointJumpIntervalPathCompletion20261011, terminal, gridNotTerminal, if_false]
    change states _ = states _
    congr 1
    apply Fin.ext
    unfold finiteJumpCountCompletion20261011
    change (Finset.univ.filter (fun index => knots index ≤ skorokhodRegularGridPointCompletion20261011 grid
      (skorokhodRegularGridSelectionCompletion20261011 grid time))).card =
        (Finset.univ.filter (fun index => roundedIntervalKnotCompletion20261011 grid (knots index) ≤ time)).card
    apply congrArg Finset.card
    apply Finset.ext
    intro index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact roundedIntervalKnot_grid_inequality_completion20261011 grid (knots index) time

theorem finiteEndpointJump_time_change_completion20261011 {count : ℕ}
    (first second : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (states : Fin (count+1) → Space) (endpoint : Space)
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (knotIdentity : ∀ index, change (first index) = second index)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    finiteEndpointJumpIntervalPathCompletion20261011 second states endpoint (change time) =
      finiteEndpointJumpIntervalPathCompletion20261011 first states endpoint time := by
  have endpointEquivalent : (change time).val = 1 ↔ time.val = 1 := by
    have identity := intervalOrderIso_one_fixed_completion20261011 change
    constructor
    · intro equal
      have typed : change time = (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011) := Subtype.ext equal
      rw [← identity] at typed
      exact congrArg Subtype.val (change.injective typed)
    · intro equal
      have typed : time = (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011) := Subtype.ext equal
      rw [typed, identity]
  simp only [finiteEndpointJumpIntervalPathCompletion20261011, endpointEquivalent]
  split_ifs
  · rfl
  · exact finiteJumpIntervalPath_time_change_completion20261011 first second states change knotIdentity time

theorem finiteEndpointJump_grid_tendsto_completion20261011 [CompactSpace Space] {count : ℕ}
    (knots : Fin count → SkorokhodIntervalTimeCompletion20261011) (increasing : StrictMono knots)
    (interior : ∀ index, 0 < (knots index).val ∧ (knots index).val < 1)
    (states : Fin (count+1) → Space) (endpoint : Space) :
    Tendsto (fun grid => skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid)
      (fun index => finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint
        (skorokhodRegularGridPointCompletion20261011 grid index))) atTop
      (𝓝 (finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint)) := by
  have increasingEventually : ∀ᶠ grid : ℕ in atTop, StrictMono (fun index => roundedIntervalKnotCompletion20261011 grid (knots index)) := by
    have pairs : ∀ first second : Fin count, ∀ᶠ grid : ℕ in atTop,
        first < second → roundedIntervalKnotCompletion20261011 grid (knots first) < roundedIntervalKnotCompletion20261011 grid (knots second) := by
      intro first second
      by_cases before : first < second
      · exact ((roundedIntervalKnot_tendsto_completion20261011 (knots first)).eventually_lt
          (roundedIntervalKnot_tendsto_completion20261011 (knots second)) (increasing before)).mono (fun _ bound _ => bound)
      · exact Eventually.of_forall (fun _ impossible => (before impossible).elim)
    exact (Filter.eventually_all.mpr (fun first => Filter.eventually_all.mpr (pairs first))).mono (fun _ pairBound => pairBound)
  have interiorEventually : ∀ᶠ grid : ℕ in atTop, ∀ index,
      0 < (roundedIntervalKnotCompletion20261011 grid (knots index)).val ∧
      (roundedIntervalKnotCompletion20261011 grid (knots index)).val < 1 := by
    apply Filter.eventually_all.mpr
    intro index
    have convergence := continuous_subtype_val.tendsto (knots index) |>.comp (roundedIntervalKnot_tendsto_completion20261011 (knots index))
    exact (convergence.eventually (Ioo_mem_nhds (interior index).1 (interior index).2))
  have errorConvergence : Tendsto (fun grid : ℕ => ((2 : ℝ)^count-1) * (1/(grid+1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using skorokhodRegularGrid_mesh_tendsto_completion20261011.const_mul ((2 : ℝ)^count-1)
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [increasingEventually, interiorEventually, errorConvergence.eventually (gt_mem_nhds positive)]
    with grid roundedIncreasing roundedInterior errorSmall
  obtain ⟨change, knotIdentity, displacement⟩ := interval_finite_knots_orderIso_completion20261011 count knots
    (fun index => roundedIntervalKnotCompletion20261011 grid (knots index)) increasing roundedIncreasing interior roundedInterior
    (1/(grid+1 : ℝ)) (fun index => by simpa only [dist_comm] using roundedIntervalKnot_distance_completion20261011 grid (knots index))
  have edistance : edist
      (finiteEndpointJumpIntervalPathCompletion20261011 (fun index => roundedIntervalKnotCompletion20261011 grid (knots index)) states endpoint)
      (finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint) ≤
      ENNReal.ofReal (((2 : ℝ)^count-1) * (1/(grid+1 : ℝ))) := by
    apply iInf_le_of_le change
    apply max_le
    · apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (displacement time)
    · apply iSup_le
      intro time
      rw [finiteEndpointJump_time_change_completion20261011 knots _ states endpoint change knotIdentity time, edist_self]
      exact zero_le
  rw [finiteEndpointJump_grid_identity_completion20261011]
  apply edist_lt_ofReal.mp
  exact edistance.trans_lt ((ENNReal.ofReal_lt_ofReal_iff positive).mpr errorSmall)

end
end IGSIII34.Diffusion
