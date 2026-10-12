import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

def stoppingCeilingTimeCompletion (index : ℕ) (time : ℝ≥0) : ℝ≥0 :=
  (⌈((index + 1 : ℕ) : ℝ≥0) * time⌉₊ : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0)

theorem stoppingCeilingTime_lower_completion (index : ℕ) (time : ℝ≥0) :
    time ≤ stoppingCeilingTimeCompletion index time := by
  have positive : (0 : ℝ≥0) < ((index + 1 : ℕ) : ℝ≥0) := by positivity
  unfold stoppingCeilingTimeCompletion
  rw [le_div_iff₀ positive]
  simpa only [mul_comm] using Nat.le_ceil (((index + 1 : ℕ) : ℝ≥0) * time)

theorem stoppingCeilingTime_upper_completion (index : ℕ) (time : ℝ≥0) :
    stoppingCeilingTimeCompletion index time < time + ((index + 1 : ℕ) : ℝ≥0)⁻¹ := by
  have positive : (0 : ℝ≥0) < ((index + 1 : ℕ) : ℝ≥0) := by positivity
  unfold stoppingCeilingTimeCompletion
  rw [div_lt_iff₀ positive]
  have rounding := Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ ((index + 1 : ℕ) : ℝ≥0) * time from zero_le)
  convert rounding using 1 <;> field_simp <;> ring

theorem stoppingCeilingTime_tendsto_completion (time : ℝ≥0) :
    Tendsto (fun index => stoppingCeilingTimeCompletion index time) atTop (𝓝 time) := by
  apply NNReal.tendsto_coe.mp
  have growing : Tendsto (fun index : ℕ => ((index + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have upperLimit : Tendsto (fun index : ℕ => (time : ℝ) + ((index + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (time : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (time : ℝ))).add (tendsto_inv_atTop_zero.comp growing)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (time : ℝ))) upperLimit
    (fun index => by exact_mod_cast stoppingCeilingTime_lower_completion index time)
    (fun index => by exact_mod_cast (stoppingCeilingTime_upper_completion index time).le)

theorem stoppingCeilingTime_measurable_completion
    {Omega : Type*} [MeasurableSpace Omega] (time : Omega → ℝ≥0) (measurable : Measurable time) (index : ℕ) :
    Measurable (fun sample => stoppingCeilingTimeCompletion index (time sample)) := by
  unfold stoppingCeilingTimeCompletion
  exact ((measurable_of_countable (fun number : ℕ => (number : ℝ≥0))).comp
    (Nat.measurable_ceil.comp (measurable_const.mul measurable))).div_const _

theorem stoppingTime_nnreal_measurable_completion
    {Omega : Type*} [MeasurableSpace Omega] (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (time : Omega → ℝ≥0) (stopping : IsStoppingTime filtration (fun sample => (time sample : WithTop ℝ≥0))) :
    Measurable time := by
  apply measurable_of_Iic
  intro point
  change MeasurableSet {sample | time sample ≤ point}
  simpa only [WithTop.coe_le_coe] using filtration.le point _ (stopping point)

theorem stoppingCeilingCell_measurable_completion
    {Omega : Type*} [MeasurableSpace Omega] (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (time : Omega → ℝ≥0) (stopping : IsStoppingTime filtration (fun sample => (time sample : WithTop ℝ≥0)))
    (event : Set Omega) (eventKnown : MeasurableSet[stopping.measurableSpace] event)
    (index number : ℕ) :
    MeasurableSet[filtration ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0))]
      (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ = number}) := by
  have positive : (0 : ℝ≥0) < ((index + 1 : ℕ) : ℝ≥0) := by positivity
  have cutoff (point : ℕ) :
      event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ point} =
        event ∩ {sample | (time sample : WithTop ℝ≥0) ≤ ((point : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) : ℝ≥0)} := by
    ext sample
    simp only [mem_inter_iff, mem_setOf_eq, WithTop.coe_le_coe, Nat.ceil_le]
    rw [le_div_iff₀ positive, mul_comm]
  have cutoffKnown (point : ℕ) :
      MeasurableSet[filtration ((point : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0))]
        (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ point}) := by
    rw [cutoff]
    exact eventKnown.2 _
  by_cases zero : number = 0
  · subst number
    simpa only [Nat.le_zero] using cutoffKnown 0
  · have previousBefore : ((number - 1 : ℕ) : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) ≤
        (number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le number 1) zero_le
    have cell : event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ = number} =
        (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ number}) \
          (event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ number - 1}) := by
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
        have previousFalse : ¬ ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ number - 1 :=
          fun previous => outside ⟨member, previous⟩
        omega
    rw [cell]
    exact (cutoffKnown number).diff (filtration.mono previousBefore _ (cutoffKnown (number - 1)))

end
end IGSIII34.Diffusion
