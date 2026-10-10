import Mathlib.Topology.Bases
import Mathlib.Data.List.Basic

/-! A countable invariant core of a separable surjective dynamical system.
This allows later almost-everywhere comparisons to be intersected countably. -/

set_option autoImplicit false

namespace IGSIII.Probability
open TopologicalSpace

private def twoSidedWords {Space : Type*} (forward backward : Space → Space)
    (seed : ℕ → Space) : ℕ × List Bool → Space
  | (index, []) => seed index
  | (index, true :: rest) => forward (twoSidedWords forward backward seed (index, rest))
  | (index, false :: rest) => backward (twoSidedWords forward backward seed (index, rest))

theorem exists_countable_dense_invariant_core {Space : Type*} [TopologicalSpace Space]
    [SeparableSpace Space] [Nonempty Space] (forward : Space → Space)
    (onto : Function.Surjective forward) :
    ∃ core : Set Space, core.Countable ∧ Dense core ∧
      Set.MapsTo forward core core ∧ Set.SurjOn forward core core := by
  classical
  let backward : Space → Space := fun value => (onto value).choose
  have rightInverse : ∀ value, forward (backward value) = value :=
    fun value => (onto value).choose_spec
  let seed : ℕ → Space := TopologicalSpace.denseSeq Space
  let core : Set Space := Set.range (twoSidedWords forward backward seed)
  refine ⟨core, Set.countable_range _, ?_, ?_, ?_⟩
  · apply (TopologicalSpace.denseRange_denseSeq Space).mono
    rintro value ⟨index, rfl⟩
    exact ⟨(index, []), by simp [twoSidedWords, seed]⟩
  · rintro value ⟨⟨index, word⟩, rfl⟩
    exact ⟨(index, true :: word), by simp [twoSidedWords]⟩
  · rintro value ⟨⟨index, word⟩, rfl⟩
    refine ⟨backward (twoSidedWords forward backward seed (index, word)), ?_, rightInverse _⟩
    exact ⟨(index, false :: word), by simp [twoSidedWords]⟩

end IGSIII.Probability


