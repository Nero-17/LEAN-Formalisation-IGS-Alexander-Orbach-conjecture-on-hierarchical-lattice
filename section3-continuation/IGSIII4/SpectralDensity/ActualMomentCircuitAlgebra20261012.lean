import IGSIII4.SpectralDensity.ActualCrossing20261012
import IGSIII4.SpectralDensity.ActualMomentCircuitFlow20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {blocks paths interior : ℕ}

def pathResistance (resistance : Edge blocks paths interior → ℝ)
    (block : Fin blocks) (path : Fin paths) : ℝ :=
  ∑ edge : Fin (interior + 2), resistance (.inr (block, path, edge))

def pathConductance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (block : Fin blocks) (path : Fin paths) : ℝ :=
  if ∀ edge : Fin (interior + 2), configuration (.inr (block, path, edge)) = true then
    (pathResistance resistance block path)⁻¹ else 0

def blockConductance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (block : Fin blocks) : ℝ :=
  ∑ path, pathConductance configuration resistance block path

def blockResistance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (block : Fin blocks) : ℝ :=
  (blockConductance configuration resistance block)⁻¹

def shortResistance (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  resistance (.inl 0) + resistance (.inl 1)

def longResistance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  resistance (.inl 2) + (∑ block, blockResistance configuration resistance block) + resistance (.inl 3)

def ShortCrosses (configuration : Edge blocks paths interior → Bool) : Prop :=
  configuration (.inl 0) = true ∧ configuration (.inl 1) = true

def LongCrosses (configuration : Edge blocks paths interior → Bool) : Prop :=
  configuration (.inl 2) = true ∧ configuration (.inl 3) = true ∧
    ChainCrosses blocks paths interior configuration

def shortConductance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  if ShortCrosses configuration then (shortResistance resistance)⁻¹ else 0

def longConductance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  if LongCrosses configuration then (longResistance configuration resistance)⁻¹ else 0

def circuitVoltage (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  (shortConductance configuration resistance + longConductance configuration resistance)⁻¹

def shortBranchCurrent (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  circuitVoltage configuration resistance * shortConductance configuration resistance

def longBranchCurrent (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : ℝ :=
  circuitVoltage configuration resistance * longConductance configuration resistance

def weightedPathCurrent (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (block : Fin blocks) (path : Fin paths) : ℝ :=
  longBranchCurrent configuration resistance * blockResistance configuration resistance block *
    pathConductance configuration resistance block path

theorem pathResistance_positive20261012 (resistance : Edge blocks paths interior → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (block : Fin blocks) (path : Fin paths) :
    0 < pathResistance resistance block path := by
  exact Finset.sum_pos (fun edge _ => positive _) Finset.univ_nonempty

theorem pathConductance_nonnegative20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (block : Fin blocks) (path : Fin paths) :
    0 ≤ pathConductance configuration resistance block path := by
  unfold pathConductance
  split_ifs
  · exact (inv_pos.mpr (pathResistance_positive20261012 resistance positive block path)).le
  · exact le_rfl

theorem blockConductance_positive20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (block : Fin blocks) (crosses : ∃ path : Fin paths, ∀ edge : Fin (interior + 2),
      configuration (.inr (block, path, edge)) = true) :
    0 < blockConductance configuration resistance block := by
  obtain ⟨path, opened⟩ := crosses
  apply Finset.sum_pos' (fun other _ => pathConductance_nonnegative20261012 configuration resistance positive block other)
  refine ⟨path, Finset.mem_univ _, ?_⟩
  simp only [pathConductance, opened, implies_true, ↓reduceIte]
  exact inv_pos.mpr (pathResistance_positive20261012 resistance positive block path)

theorem blockResistance_nonnegative20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (block : Fin blocks) : 0 ≤ blockResistance configuration resistance block := by
  apply inv_nonneg.mpr
  exact Finset.sum_nonneg (fun path _ => pathConductance_nonnegative20261012 configuration resistance positive block path)

theorem longResistance_positive20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    0 < longResistance configuration resistance := by
  have middle : 0 ≤ ∑ block : Fin blocks, blockResistance configuration resistance block :=
    Finset.sum_nonneg (fun block _ => blockResistance_nonnegative20261012 configuration resistance positive block)
  unfold longResistance
  linarith [positive (.inl 2), positive (.inl 3)]

theorem circuitConductance_positive20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    0 < shortConductance configuration resistance + longConductance configuration resistance := by
  have shortPositive : 0 < shortResistance resistance := add_pos (positive (.inl 0)) (positive (.inl 1))
  have longPositive := longResistance_positive20261012 configuration resistance positive
  rcases crosses with short | long
  · have shortTrue : ShortCrosses configuration := short
    simp only [shortConductance, shortTrue, ↓reduceIte, longConductance]
    split_ifs <;> positivity
  · have longTrue : LongCrosses configuration := long
    simp only [longConductance, longTrue, ↓reduceIte, shortConductance]
    split_ifs <;> positivity

theorem branchCurrent_total20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    shortBranchCurrent configuration resistance + longBranchCurrent configuration resistance = 1 := by
  rw [shortBranchCurrent, longBranchCurrent, ← mul_add, circuitVoltage]
  exact inv_mul_cancel₀ (ne_of_gt (circuitConductance_positive20261012 configuration resistance positive crosses))

theorem weightedPathCurrent_block_sum20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (block : Fin blocks) :
    (∑ path, weightedPathCurrent configuration resistance block path) =
      longBranchCurrent configuration resistance := by
  simp only [weightedPathCurrent, ← Finset.mul_sum]
  change longBranchCurrent configuration resistance * (blockConductance configuration resistance block)⁻¹ *
    blockConductance configuration resistance block = _
  by_cases long : LongCrosses configuration
  · have nonzero := ne_of_gt (blockConductance_positive20261012 configuration resistance positive block (long.2.2 block))
    rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]
  · simp [longBranchCurrent, longConductance, long]

end
end IGSIII4.SpectralDensity.ActualFamily
