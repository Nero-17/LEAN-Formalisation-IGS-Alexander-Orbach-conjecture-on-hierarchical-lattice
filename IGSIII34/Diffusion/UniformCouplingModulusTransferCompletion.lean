import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

/-- Compact-time closeness in a genuine coupling transfers a proved
modulus estimate. Both bad events remain on the original sample space. -/
theorem uniform_coupling_transfers_physical_modulus_completion
    {Space : Type*} [MetricSpace Space]
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsFiniteMeasure (laws index)]
    (samples references : ∀ index, Samples index → ℝ≥0 → Space)
    (modulus : ∀ horizon : ℝ≥0, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon →
            dist first second < duration → dist (references index outcome first) (references index outcome second) ≤ tolerance)
    (coupling : ∀ horizon : ℝ≥0, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∀ᶠ index in atTop, ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
        ∀ outcome ∉ bad, ∀ time : ℝ≥0, time ≤ horizon → dist (samples index outcome time) (references index outcome time) ≤ tolerance)
    (horizon : ℝ≥0) (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
      ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
        ∀ outcome ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon →
          dist first second < duration → dist (samples index outcome first) (samples index outcome second) ≤ tolerance := by
  obtain ⟨duration, durationPositive, referenceBounds⟩ := modulus horizon (tolerance/3) (error/2) (by positivity) (by positivity)
  refine ⟨duration, durationPositive, ?_⟩
  filter_upwards [referenceBounds, coupling horizon (tolerance/3) (error/2) (by positivity) (by positivity)]
    with index referenceBound couplingBound
  obtain ⟨referenceBad, referenceMeasurable, referenceProbability, referenceGood⟩ := referenceBound
  obtain ⟨couplingBad, couplingMeasurable, couplingProbability, couplingGood⟩ := couplingBound
  refine ⟨referenceBad ∪ couplingBad, referenceMeasurable.union couplingMeasurable,
    (measureReal_union_le _ _).trans (by linarith), ?_⟩
  intro outcome outside first second firstBound secondBound near
  have referenceOutside : outcome ∉ referenceBad := fun member => outside (Or.inl member)
  have couplingOutside : outcome ∉ couplingBad := fun member => outside (Or.inr member)
  have firstNear := couplingGood outcome couplingOutside first firstBound
  have secondNear := couplingGood outcome couplingOutside second secondBound
  have middle := referenceGood outcome referenceOutside first second firstBound secondBound near
  have triangle := (dist_triangle (samples index outcome first) (references index outcome first) (samples index outcome second)).trans
    (add_le_add le_rfl (dist_triangle (references index outcome first) (references index outcome second) (samples index outcome second)))
  rw [dist_comm (samples index outcome second) (references index outcome second)] at secondNear
  linarith

end
end IGSIII34.Diffusion
