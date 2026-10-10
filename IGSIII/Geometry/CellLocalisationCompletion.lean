import IGSIII.Geometry.CellLocalisationCone
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open UniformSpace

variable {Intrinsic Ambient : Type*} [MetricSpace Intrinsic] [MetricSpace Ambient] [CompleteSpace Ambient]

/-- Boundary cone localisation and injectivity on its available anchors imply
injectivity on the entire metric cell, also when the anchors coincide. -/
theorem cell_injective_of_boundary_localisation (inclusion : Intrinsic → Ambient)
    (source target : Intrinsic)
    (localisation : ∀ first last : Intrinsic,
      min (min (dist first source) (dist first target)) (dist first last) ≤
        dist (inclusion first) (inclusion last))
    (boundary_injective : inclusion source = inclusion target → source = target) :
    Function.Injective inclusion := by
  intro first last same_image
  by_cases equal : first = last
  · exact equal
  have boundary (first last : Intrinsic) (different : first ≠ last)
      (same_image : inclusion first = inclusion last) : first = source ∨ first = target := by
    by_contra interior
    push Not at interior
    have strictly_positive := lt_min
      (lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)) (dist_pos.mpr different)
    have bound := localisation first last
    rw [same_image, dist_self] at bound
    exact (not_lt_of_ge bound) strictly_positive
  have first_boundary := boundary first last equal same_image
  have last_boundary := boundary last first (Ne.symm equal) same_image.symm
  rcases first_boundary with rfl | rfl <;> rcases last_boundary with rfl | rfl
  · rfl
  · exact boundary_injective same_image
  · exact (boundary_injective same_image.symm).symm
  · rfl
/-- The finite cone localisation estimate survives metric completion by
continuity of the actual Lipschitz extension. -/
theorem completion_cell_localisation (inclusion : Intrinsic → Ambient)
    (lipschitz : LipschitzWith 1 inclusion) (source target : Intrinsic)
    (localisation : ∀ first last : Intrinsic,
      min (min (dist first source) (dist first target)) (dist first last) ≤
        dist (inclusion first) (inclusion last))
    (first last : Completion Intrinsic) :
    min (min (dist first (source : Completion Intrinsic)) (dist first (target : Completion Intrinsic))) (dist first last) ≤
      dist (Completion.extension inclusion first) (Completion.extension inclusion last) := by
  refine Completion.induction_on₂ first last
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro first last
  simpa only [Completion.extension_coe lipschitz.uniformContinuous, Completion.dist_eq] using localisation first last

/-- Localisation prevents any new identification of interior points. -/
theorem completion_cell_equal_image (inclusion : Intrinsic → Ambient)
    (lipschitz : LipschitzWith 1 inclusion) (source target : Intrinsic)
    (localisation : ∀ first last : Intrinsic,
      min (min (dist first source) (dist first target)) (dist first last) ≤
        dist (inclusion first) (inclusion last))
    {first last : Completion Intrinsic}
    (same_image : Completion.extension inclusion first = Completion.extension inclusion last) :
    first = last ∨ ((first = source ∨ first = target) ∧ (last = source ∨ last = target)) := by
  by_cases equal : first = last
  · exact Or.inl equal
  have boundary (first last : Completion Intrinsic) (different : first ≠ last)
      (same_image : Completion.extension inclusion first = Completion.extension inclusion last) :
      first = source ∨ first = target := by
    by_contra interior
    push Not at interior
    have strictly_positive := lt_min
      (lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)) (dist_pos.mpr different)
    have bound := completion_cell_localisation inclusion lipschitz source target localisation first last
    rw [same_image, dist_self] at bound
    exact (not_lt_of_ge bound) strictly_positive
  exact Or.inr ⟨boundary first last equal same_image, boundary last first (Ne.symm equal) same_image.symm⟩

theorem completion_cell_injective (inclusion : Intrinsic → Ambient)
    (lipschitz : LipschitzWith 1 inclusion) (source target : Intrinsic)
    (localisation : ∀ first last : Intrinsic,
      min (min (dist first source) (dist first target)) (dist first last) ≤
        dist (inclusion first) (inclusion last))
    (boundary_distinct : inclusion source ≠ inclusion target) :
    Function.Injective (Completion.extension inclusion) := by
  intro first last same_image
  rcases completion_cell_equal_image inclusion lipschitz source target localisation same_image with equal | boundary
  · exact equal
  rcases boundary.1 with rfl | rfl <;> rcases boundary.2 with rfl | rfl
  · rfl
  · exact False.elim (boundary_distinct (by simpa only [Completion.extension_coe lipschitz.uniformContinuous] using same_image))
  · exact False.elim (boundary_distinct (by simpa only [Completion.extension_coe lipschitz.uniformContinuous] using same_image.symm))
  · rfl

/-- The boundary condition also allows a one-sided noncrossing component,
whose two available boundary labels name the same planted point. -/
theorem completion_cell_injective_of_boundary_injective (inclusion : Intrinsic → Ambient)
    (lipschitz : LipschitzWith 1 inclusion) (source target : Intrinsic)
    (localisation : ∀ first last : Intrinsic,
      min (min (dist first source) (dist first target)) (dist first last) ≤
        dist (inclusion first) (inclusion last))
    (boundary_injective : inclusion source = inclusion target → source = target) :
    Function.Injective (Completion.extension inclusion) := by
  intro first last same_image
  rcases completion_cell_equal_image inclusion lipschitz source target localisation same_image with equal | boundary
  · exact equal
  rcases boundary.1 with rfl | rfl <;> rcases boundary.2 with rfl | rfl
  · rfl
  · exact congrArg (fun point : Intrinsic => (point : Completion Intrinsic))
      (boundary_injective (by simpa only [Completion.extension_coe lipschitz.uniformContinuous] using same_image))
  · exact congrArg (fun point : Intrinsic => (point : Completion Intrinsic))
      (boundary_injective (by simpa only [Completion.extension_coe lipschitz.uniformContinuous] using same_image.symm)).symm
  · rfl
variable {Other : Type*} [MetricSpace Other]

/-- Distinct cell images can meet only at planted boundary points, once the
proved finite boundary-sum estimate is passed to the two completions. -/
theorem completion_distinct_cells_intersection
    (first_inclusion : Intrinsic → Ambient) (last_inclusion : Other → Ambient)
    (first_lipschitz : LipschitzWith 1 first_inclusion) (last_lipschitz : LipschitzWith 1 last_inclusion)
    (first_source first_target : Intrinsic) (last_source last_target : Other)
    (separation : ∀ first : Intrinsic, ∀ last : Other,
      min (dist first first_source) (dist first first_target) +
        min (dist last last_source) (dist last last_target) ≤
          dist (first_inclusion first) (last_inclusion last))
    {first : Completion Intrinsic} {last : Completion Other}
    (same_image : Completion.extension first_inclusion first = Completion.extension last_inclusion last) :
    (first = first_source ∨ first = first_target) ∧ (last = last_source ∨ last = last_target) := by
  have completed_separation (first : Completion Intrinsic) (last : Completion Other) :
      min (dist first (first_source : Completion Intrinsic)) (dist first (first_target : Completion Intrinsic)) +
        min (dist last (last_source : Completion Other)) (dist last (last_target : Completion Other)) ≤
          dist (Completion.extension first_inclusion first) (Completion.extension last_inclusion last) := by
    induction first using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih first =>
      induction last using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih last =>
        simpa only [Completion.extension_coe first_lipschitz.uniformContinuous,
          Completion.extension_coe last_lipschitz.uniformContinuous, Completion.dist_eq] using separation first last
  have bound := completed_separation first last
  rw [same_image, dist_self] at bound
  have first_nonnegative : 0 ≤ min (dist first (first_source : Completion Intrinsic)) (dist first (first_target : Completion Intrinsic)) :=
    le_min dist_nonneg dist_nonneg
  have last_nonnegative : 0 ≤ min (dist last (last_source : Completion Other)) (dist last (last_target : Completion Other)) :=
    le_min dist_nonneg dist_nonneg
  constructor
  · by_contra interior
    push Not at interior
    have strictly_positive := lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)
    linarith
  · by_contra interior
    push Not at interior
    have strictly_positive := lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)
    linarith

end
end IGSIII.Geometry



