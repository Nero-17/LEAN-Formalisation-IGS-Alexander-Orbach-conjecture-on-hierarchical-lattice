import IGSIII34.Diffusion.StoppingCeilingApproximationCompletion20261011
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

theorem stoppingCeilingWithTopCell_measurable_completion20261011
    {Omega : Type*} [MeasurableSpace Omega] (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (time : Omega → WithTop ℝ≥0) (stopping : IsStoppingTime filtration time)
    (event : Set Omega) (eventKnown : MeasurableSet[stopping.measurableSpace] event)
    (finiteOn : ∀ sample, sample ∈ event → time sample ≠ ⊤)
    (index number : ℕ) :
    MeasurableSet[filtration ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0))]
      (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ = number}) := by
  have positive : (0 : ℝ≥0) < ((index + 1 : ℕ) : ℝ≥0) := by positivity
  have cutoff (point : ℕ) :
      event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ ≤ point} =
        event ∩ {sample | time sample ≤ ((point : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) : ℝ≥0)} := by
    ext sample
    simp only [mem_inter_iff, mem_setOf_eq, Nat.ceil_le]
    constructor
    · rintro ⟨member, bounded⟩
      exact ⟨member, (WithTop.untopA_le_iff (finiteOn sample member)).mp ((le_div_iff₀ positive).mpr (by simpa only [mul_comm] using bounded))⟩
    · rintro ⟨member, bounded⟩
      exact ⟨member, by simpa only [mul_comm] using (le_div_iff₀ positive).mp ((WithTop.untopA_le_iff (finiteOn sample member)).mpr bounded)⟩
  have cutoffKnown (point : ℕ) :
      MeasurableSet[filtration ((point : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0))]
        (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ ≤ point}) := by
    rw [cutoff]
    exact eventKnown.2 _
  by_cases zero : number = 0
  · subst number
    simpa only [Nat.le_zero] using cutoffKnown 0
  · have previousBefore : ((number - 1 : ℕ) : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) ≤
        (number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le number 1) zero_le
    have cell : event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ = number} =
        (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ ≤ number}) \
          (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ ≤ number - 1}) := by
      ext sample
      simp only [mem_inter_iff, mem_setOf_eq, Set.mem_sdiff]
      have positiveNumber : 0 < number := Nat.pos_of_ne_zero zero
      constructor
      · rintro ⟨member, equality⟩
        refine ⟨⟨member, equality.le⟩, ?_⟩
        rintro ⟨_, previous⟩
        rw [equality] at previous
        omega
      · rintro ⟨⟨member, upper⟩, outside⟩
        refine ⟨member, ?_⟩
        have previousFalse : ¬ ⌈((index + 1 : ℕ) : ℝ≥0) * (time sample).untopA⌉₊ ≤ number - 1 :=
          fun previous => outside ⟨member, previous⟩
        omega
    rw [cell]
    exact (cutoffKnown number).diff (filtration.mono previousBefore _ (cutoffKnown (number - 1)))

end
end IGSIII34.Diffusion

