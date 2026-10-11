import IGSIII34.Diffusion.CountableWeakUniqueLimitCompletion20261011
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- Compactness and the genuine uniqueness of projective measures turn
finite marginal weak convergence into countable product weak convergence. -/
theorem countableTimeLaws_weak_of_finite_marginals_completion20261011
    (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (target : ProbabilityMeasure (ℕ → Space))
    (finiteMarginals : ∀ count : ℕ, ∀ coordinates : Fin count → ℕ,
      Tendsto (fun depth => (laws depth).map
        (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index))
          (laws depth) from (by fun_prop : Measurable _).aemeasurable))
        atTop (𝓝 (target.map
          (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index))
            target from (by fun_prop : Measurable _).aemeasurable)))) :
    Tendsto laws atTop (𝓝 target) := by
  classical
  apply countableTimeLaws_tendsto_of_unique_subsequential_limits_completion20261011 laws target
  intro selected strict candidate weak
  have equalFinite (count : ℕ) (coordinates : Fin count → ℕ) :
      (candidate : Measure (ℕ → Space)).map (fun path => fun index : Fin count => path (coordinates index)) =
        (target : Measure (ℕ → Space)).map (fun path => fun index : Fin count => path (coordinates index)) := by
    have first := countableTimeLaws_finite_marginals_completion20261011
      (fun index => laws (selected index)) candidate weak coordinates
    have second := (finiteMarginals count coordinates).comp strict.tendsto_atTop
    exact congrArg (fun law : ProbabilityMeasure (Fin count → Space) => (law : Measure (Fin count → Space)))
      (tendsto_nhds_unique first second)
  have allFinite (set : Finset ℕ) : (candidate : Measure (ℕ → Space)).map set.restrict =
      (target : Measure (ℕ → Space)).map set.restrict := by
    let enumeration := Fintype.equivFin set
    let coordinates : Fin (Fintype.card set) → ℕ := fun index => (enumeration.symm index).val
    let reindex : (Fin (Fintype.card set) → Space) → set → Space :=
      fun values coordinate => values (enumeration coordinate)
    have restriction : set.restrict (π := fun _ : ℕ => Space) =
        reindex ∘ (fun path : ℕ → Space => fun index => path (coordinates index)) := by
      funext path coordinate
      simp only [reindex, coordinates, Function.comp_apply, Equiv.symm_apply_apply, Finset.restrict]
    rw [restriction, ← Measure.map_map (by fun_prop : Measurable reindex) (by fun_prop),
      ← Measure.map_map (by fun_prop : Measurable reindex) (by fun_prop), equalFinite]
  apply Subtype.ext
  have first : IsProjectiveLimit (α := fun _ : ℕ => Space) (candidate : Measure (ℕ → Space))
      (fun set => (candidate : Measure (ℕ → Space)).map set.restrict) := fun _ => rfl
  have second : IsProjectiveLimit (α := fun _ : ℕ => Space) (target : Measure (ℕ → Space))
      (fun set => (candidate : Measure (ℕ → Space)).map set.restrict) := fun set => (allFinite set).symm
  exact first.unique second

end
end IGSIII34.Diffusion
