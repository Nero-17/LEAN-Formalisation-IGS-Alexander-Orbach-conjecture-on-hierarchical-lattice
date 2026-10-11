import IGSIII34.ResistanceLimit.LimitEnergy
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false
namespace IGSIII34.Forms
noncomputable section
open Filter
open scoped _root_.Topology BigOperators

/-- A finite partition of nonnegative trace energies passes to their
monotone limits. A fixed shift permits components born at a later depth.
Local boundedness is derived from global finite energy. -/
theorem component_trace_supremum_decomposition
    {Component : Type*} [Fintype Component]
    (total : ℕ → ℝ) (component : Component → ℕ → ℝ) (age : ℕ)
    (nonnegative : ∀ cell depth, 0 ≤ component cell depth)
    (monotone : ∀ cell, Monotone (component cell))
    (totalMonotone : Monotone total)
    (partition : ∀ depth, total (depth + age) = ∑ cell, component cell depth)
    (finite : BddAbove (Set.range total)) :
    (∀ cell, BddAbove (Set.range (component cell))) ∧
      (⨆ depth, total depth) = ∑ cell, ⨆ depth, component cell depth ∧
      ∀ cell, 0 ≤ (⨆ depth, component cell depth) ∧
        (⨆ depth, component cell depth) ≤ ⨆ depth, total depth := by
  classical
  have bounded (cell : Component) : BddAbove (Set.range (component cell)) := by
    obtain ⟨upper, upperBound⟩ := finite
    refine ⟨upper, ?_⟩
    rintro value ⟨depth, rfl⟩
    have cellBound : component cell depth ≤ ∑ cell, component cell depth :=
      Finset.single_le_sum (fun cell _ => nonnegative cell depth) (Finset.mem_univ cell)
    rw [← partition] at cellBound
    exact cellBound.trans (upperBound (Set.mem_range_self (depth + age)))
  have totalLimit := (tendsto_atTop_ciSup totalMonotone finite).comp (tendsto_add_atTop_nat age)
  have sumLimit : Tendsto (fun depth => ∑ cell, component cell depth) atTop
      (𝓝 (∑ cell, ⨆ depth, component cell depth)) := by
    apply tendsto_finsetSum
    intro cell _
    exact tendsto_atTop_ciSup (monotone cell) (bounded cell)
  have identity : (⨆ depth, total depth) = ∑ cell, ⨆ depth, component cell depth := by
    apply tendsto_nhds_unique totalLimit
    change Tendsto (fun depth => total (depth + age)) atTop _
    simp_rw [partition]
    exact sumLimit
  refine ⟨bounded, identity, ?_⟩
  intro cell
  have positive (other : Component) : 0 ≤ ⨆ depth, component other depth :=
    (nonnegative other 0).trans (le_ciSup (bounded other) 0)
  refine ⟨positive cell, ?_⟩
  rw [identity]
  exact Finset.single_le_sum (fun other _ => positive other) (Finset.mem_univ cell)

/-- Zero extension preserves limiting energy once the genuine finite
component trace identities have been established. -/
theorem component_zero_extension_energy
    (globalTrace localTrace : ℕ → ℝ) (age : ℕ)
    (globalMonotone : Monotone globalTrace)
    (localMonotone : Monotone localTrace)
    (identity : ∀ depth, globalTrace (depth + age) = localTrace depth)
    (localFinite : BddAbove (Set.range localTrace)) :
    BddAbove (Set.range globalTrace) ∧
      (⨆ depth, globalTrace depth) = ⨆ depth, localTrace depth := by
  obtain ⟨upper, upperBound⟩ := localFinite
  have globalFinite : BddAbove (Set.range globalTrace) := by
    refine ⟨upper, ?_⟩
    rintro value ⟨depth, rfl⟩
    have estimate := globalMonotone (Nat.le_add_right depth age)
    rw [identity] at estimate
    exact estimate.trans (upperBound (Set.mem_range_self depth))
  refine ⟨globalFinite, ?_⟩
  apply tendsto_nhds_unique
    ((tendsto_atTop_ciSup globalMonotone globalFinite).comp (tendsto_add_atTop_nat age))
  change Tendsto (fun depth => globalTrace (depth + age)) atTop _
  simp_rw [identity]
  exact tendsto_atTop_ciSup localMonotone
    (show BddAbove (Set.range localTrace) from ⟨upper, upperBound⟩)

end
end IGSIII34.Forms
