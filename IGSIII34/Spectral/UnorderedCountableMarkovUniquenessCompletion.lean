import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

/-! Countable Markov laws with arbitrarily enumerated observation times.
Every finite joint law is recovered by deleting a latest noninitial time;
no ordering of the enumeration is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Space : Type*} [MeasurableSpace Space] [StandardBorelSpace Space] [Nonempty Space]

theorem unordered_countable_law_eq_of_initial_and_conditional_kernels_completion
    (first second : Measure (ℕ → Space)) [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0)
    (transition : ℝ≥0 → Kernel Space Space) [∀ time, IsFiniteKernel (transition time)]
    (initial : first.map (fun path => path 0) = second.map (fun path => path 0))
    (firstConditional : ∀ {count : ℕ} (coordinates : Fin count → ℕ) (present : Fin count) (future : ℕ),
      (∀ coordinate, times (coordinates coordinate) ≤ times (coordinates present)) →
      times (coordinates present) ≤ times future →
      condDistrib (fun path : ℕ → Space => path future)
        (fun path : ℕ → Space => fun coordinate : Fin count => path (coordinates coordinate)) first =ᵐ[
          first.map (fun path : ℕ → Space => fun coordinate : Fin count => path (coordinates coordinate))]
        (transition (times future - times (coordinates present))).comap
          (fun history => history present) (measurable_pi_apply present))
    (secondConditional : ∀ {count : ℕ} (coordinates : Fin count → ℕ) (present : Fin count) (future : ℕ),
      (∀ coordinate, times (coordinates coordinate) ≤ times (coordinates present)) →
      times (coordinates present) ≤ times future →
      condDistrib (fun path : ℕ → Space => path future)
        (fun path : ℕ → Space => fun coordinate : Fin count => path (coordinates coordinate)) second =ᵐ[
          second.map (fun path : ℕ → Space => fun coordinate : Fin count => path (coordinates coordinate))]
        (transition (times future - times (coordinates present))).comap
          (fun history => history present) (measurable_pi_apply present)) :
    first = second := by
  classical
  have withInitial : ∀ set : Finset ℕ, 0 ∈ set → first.map set.restrict = second.map set.restrict := by
    intro set
    induction set using Finset.strongInductionOn with
    | _ set inductionHypothesis =>
      intro containsZero
      by_cases onlyZero : set.erase 0 = ∅
      · have coordinatesZero : ∀ coordinate : set, coordinate.val = 0 := by
          intro coordinate
          by_contra different
          have member : coordinate.val ∈ set.erase 0 := Finset.mem_erase.mpr ⟨different, coordinate.property⟩
          rw [onlyZero] at member
          exact Finset.notMem_empty _ member
        have restriction : set.restrict = (fun value : Space => fun _ : set => value) ∘ (fun path : ℕ → Space => path 0) := by
          funext path coordinate
          simp only [Finset.restrict, Function.comp_apply, coordinatesZero coordinate]
        have constantMeasurable : Measurable (fun value : Space => fun _ : set => value) := by fun_prop
        rw [restriction, ← Measure.map_map constantMeasurable (measurable_pi_apply 0),
          ← Measure.map_map constantMeasurable (measurable_pi_apply 0), initial]
      · obtain ⟨future, futureMember, futureMaximal⟩ :=
          (set.erase 0).exists_max_image times (Finset.nonempty_iff_ne_empty.mpr onlyZero)
        have futureInSet := (Finset.mem_erase.mp futureMember).2
        have futureNonzero := (Finset.mem_erase.mp futureMember).1
        let historySet := set.erase future
        have zeroInHistory : 0 ∈ historySet := Finset.mem_erase.mpr ⟨Ne.symm futureNonzero, containsZero⟩
        obtain ⟨present, presentMember, presentMaximal⟩ := historySet.exists_max_image times ⟨0, zeroInHistory⟩
        have presentBefore : times present ≤ times future := by
          by_cases presentZero : present = 0
          · simp only [presentZero, timeZero]
            exact zero_le
          · exact futureMaximal present (Finset.mem_erase.mpr ⟨presentZero, (Finset.mem_erase.mp presentMember).2⟩)
        let enumeration := (Fintype.equivFin historySet).symm
        let coordinates : Fin (Fintype.card historySet) → ℕ := fun coordinate => (enumeration coordinate).val
        let presentIndex : Fin (Fintype.card historySet) := enumeration.symm ⟨present, presentMember⟩
        have coordinatesPresent : coordinates presentIndex = present := by
          simp [coordinates, presentIndex]
        have allBefore : ∀ coordinate, times (coordinates coordinate) ≤ times (coordinates presentIndex) := by
          intro coordinate
          rw [coordinatesPresent]
          exact presentMaximal _ (enumeration coordinate).property
        have ordered : times (coordinates presentIndex) ≤ times future := by rw [coordinatesPresent]; exact presentBefore
        let history : (ℕ → Space) → (Fin (Fintype.card historySet) → Space) :=
          fun path coordinate => path (coordinates coordinate)
        have historyMeasurable : Measurable history := by fun_prop
        have historyLaw : first.map history = second.map history := by
          have restrictLaw := inductionHypothesis historySet (Finset.erase_ssubset futureInSet) zeroInHistory
          have reindex : history = (fun values : historySet → Space => fun coordinate => values (enumeration coordinate)) ∘ historySet.restrict := rfl
          rw [reindex, ← Measure.map_map (by fun_prop) (by fun_prop),
            ← Measure.map_map (by fun_prop) (by fun_prop), restrictLaw]
        let step := (transition (times future - times (coordinates presentIndex))).comap
          (fun values : Fin (Fintype.card historySet) → Space => values presentIndex) (measurable_pi_apply presentIndex)
        have firstJoint := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := first) history
          (measurable_pi_apply future).aemeasurable step).mp (firstConditional coordinates presentIndex future allBefore ordered)
        have secondJoint := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := second) history
          (measurable_pi_apply future).aemeasurable step).mp (secondConditional coordinates presentIndex future allBefore ordered)
        have jointLaw : first.map (fun path => (history path, path future)) = second.map (fun path => (history path, path future)) := by
          rw [firstJoint, secondJoint, historyLaw]
        let append : ((Fin (Fintype.card historySet) → Space) × Space) → (set → Space) :=
          fun pair coordinate => if equal : coordinate.val = future then pair.2
            else pair.1 (enumeration.symm ⟨coordinate.val, Finset.mem_erase.mpr ⟨equal, coordinate.property⟩⟩)
        have appendMeasurable : Measurable append := by
          apply measurable_pi_lambda
          intro coordinate
          by_cases equal : coordinate.val = future
          · simp only [append, dif_pos equal]
            exact measurable_snd
          · simp only [append, dif_neg equal]
            exact (measurable_pi_apply _).comp measurable_fst
        have appended : append ∘ (fun path : ℕ → Space => (history path, path future)) = set.restrict := by
          funext path coordinate
          dsimp only [Function.comp_apply, append]
          split_ifs with equal
          · simp only [Finset.restrict, equal]
          · simp [history, coordinates, Finset.restrict]
        rw [← appended, ← Measure.map_map appendMeasurable (historyMeasurable.prodMk (measurable_pi_apply future)),
          ← Measure.map_map appendMeasurable (historyMeasurable.prodMk (measurable_pi_apply future)), jointLaw]
  have allFinite : ∀ set : Finset ℕ, first.map set.restrict = second.map set.restrict := by
    intro set
    have containing := withInitial (insert 0 set) (Finset.mem_insert_self _ _)
    have smaller : set.restrict (π := fun _ : ℕ => Space) =
        Finset.restrict₂ (π := fun _ : ℕ => Space) (Finset.subset_insert 0 set) ∘ (insert 0 set).restrict := rfl
    rw [smaller, ← Measure.map_map (Finset.measurable_restrict₂ _) (by fun_prop),
      ← Measure.map_map (Finset.measurable_restrict₂ _) (by fun_prop), containing]
  have firstLimit : IsProjectiveLimit (α := fun _ : ℕ => Space) first (fun set => first.map set.restrict) := fun _ => rfl
  have secondLimit : IsProjectiveLimit (α := fun _ : ℕ => Space) second (fun set => first.map set.restrict) := fun set => (allFinite set).symm
  exact firstLimit.unique secondLimit

end
end IGSIII34.Spectral
