import IGSIII.Probability.CompactApproximation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

namespace IGSIII.Probability

open Set

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem compact_closure_bounded_scalings (sequence : ℕ → Space)
    (precompact : IsCompact (closure (Set.range sequence)))
    (scalar : ℕ → ℝ) (lower upper : ℝ)
    (bounds : ∀ depth, lower ≤ scalar depth ∧ scalar depth ≤ upper) :
    IsCompact (closure (Set.range (fun depth => scalar depth • sequence depth))) := by
  let container : Set Space :=
    (fun pair : ℝ × Space => pair.1 • pair.2) '' (Set.Icc lower upper ×ˢ closure (Set.range sequence))
  have compact : IsCompact container :=
    (isCompact_Icc.prod precompact).image (continuous_fst.smul continuous_snd)
  apply compact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ compact.isClosed
  rintro point ⟨depth, rfl⟩
  exact ⟨(scalar depth, sequence depth), ⟨bounds depth, subset_closure ⟨depth, rfl⟩⟩, rfl⟩

theorem compact_closure_seed_and_tail (sequence : ℕ → Space) (seed : Space)
    (tail : ℕ → Space) (precompact : IsCompact (closure (Set.range tail)))
    (zero : sequence 0 = seed) (successor : ∀ depth, sequence (depth + 1) = tail depth) :
    IsCompact (closure (Set.range sequence)) := by
  have compact : IsCompact ({seed} ∪ closure (Set.range tail)) := isCompact_singleton.union precompact
  apply compact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ compact.isClosed
  rintro point ⟨depth, rfl⟩
  cases depth with
  | zero => exact Or.inl (by simp [zero])
  | succ depth => exact Or.inr (by rw [successor]; exact subset_closure ⟨depth, rfl⟩)

end IGSIII.Probability

