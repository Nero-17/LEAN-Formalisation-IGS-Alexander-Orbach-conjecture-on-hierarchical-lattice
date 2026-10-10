import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Sequences

/-! Uniform approximation by compact finite-dimensional sets implies compactness.
Actual conditional expectations and their error estimates are supplied separately. -/

set_option autoImplicit false

namespace IGSIII.Probability

open Set Filter Metric
open scoped Topology

variable {Space : Type*} [MetricSpace Space]

theorem totallyBounded_of_compact_approximations (set : Set Space)
    (approximatingSets : ℕ → Set Space) (error : ℕ → ℝ)
    (compact : ∀ depth, IsCompact (approximatingSets depth))
    (vanishing : Tendsto error atTop (𝓝 0))
    (approximation : ∀ depth point, point ∈ set →
      ∃ anchor ∈ approximatingSets depth, dist point anchor ≤ error depth) :
    TotallyBounded set := by
  apply Metric.totallyBounded_iff.mpr
  intro tolerance positive
  have halfPositive : 0 < tolerance / 2 := by positivity
  obtain ⟨depth, small⟩ := eventually_atTop.mp
    ((tendsto_order.mp vanishing).2 (tolerance / 2) halfPositive)
  obtain ⟨centers, _, finite, covering⟩ :=
    (compact depth).finite_cover_balls halfPositive
  refine ⟨centers, finite, ?_⟩
  intro point membership
  obtain ⟨anchor, anchorMember, close⟩ := approximation depth point membership
  obtain ⟨center, centerCovered⟩ := Set.mem_iUnion.mp (covering anchorMember)
  obtain ⟨centerMember, centerClose⟩ := Set.mem_iUnion.mp centerCovered
  apply Set.mem_iUnion.mpr
  refine ⟨center, Set.mem_iUnion.mpr ⟨centerMember, ?_⟩⟩
  change dist point center < tolerance
  have centerDistance : dist anchor center < tolerance / 2 := centerClose
  have pointDistance : dist point anchor < tolerance / 2 := close.trans_lt (small depth le_rfl)
  calc
    _ ≤ dist point anchor + dist anchor center := dist_triangle _ _ _
    _ < tolerance / 2 + tolerance / 2 := add_lt_add pointDistance centerDistance
    _ = _ := by ring

theorem compact_closure_of_compact_approximations [CompleteSpace Space]
    (set : Set Space) (approximatingSets : ℕ → Set Space) (error : ℕ → ℝ)
    (compact : ∀ depth, IsCompact (approximatingSets depth))
    (vanishing : Tendsto error atTop (𝓝 0))
    (approximation : ∀ depth point, point ∈ set →
      ∃ anchor ∈ approximatingSets depth, dist point anchor ≤ error depth) :
    IsCompact (closure set) :=
  (totallyBounded_of_compact_approximations set approximatingSets error compact vanishing
    approximation).closure.isCompact_of_isClosed isClosed_closure

end IGSIII.Probability
