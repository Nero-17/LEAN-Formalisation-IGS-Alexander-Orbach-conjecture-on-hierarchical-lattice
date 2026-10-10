import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The numerical conclusions of Sections 3 and 4

These statements prove the dimension algebra for actual real parameters. They
do not assert the existence or comparison of the random model's growth factors.
Those model identifications must be supplied by the electrical and geometric
modules before the manuscript's unconditional theorems can be recovered.
-/

set_option autoImplicit false

namespace IGSIII34

noncomputable section

def chemicalMassDimension (massGrowth chemicalGrowth : ℝ) : ℝ :=
  Real.log massGrowth / Real.log chemicalGrowth

def chemicalResistanceDimension (resistanceGrowth chemicalGrowth : ℝ) : ℝ :=
  Real.log resistanceGrowth / Real.log chemicalGrowth

def typicalSpectralDimension (massGrowth resistanceGrowth : ℝ) : ℝ :=
  2 * Real.log massGrowth / Real.log (massGrowth * resistanceGrowth)

def dimensionRatio (massDimension resistanceDimension : ℝ) : ℝ :=
  2 * massDimension / (massDimension + resistanceDimension)

theorem dimensionRatio_eq_four_thirds_iff {massDimension resistanceDimension : ℝ}
    (positiveSum : 0 < massDimension + resistanceDimension) :
    dimensionRatio massDimension resistanceDimension = (4 / 3 : ℝ) ↔
      massDimension = 2 * resistanceDimension := by
  unfold dimensionRatio
  rw [div_eq_iff (ne_of_gt positiveSum)]
  constructor <;> intro equality <;> linarith

theorem dimensionRatio_gt_four_thirds_iff {massDimension resistanceDimension : ℝ}
    (positiveSum : 0 < massDimension + resistanceDimension) :
    (4 / 3 : ℝ) < dimensionRatio massDimension resistanceDimension ↔
      2 * resistanceDimension < massDimension := by
  unfold dimensionRatio
  rw [lt_div_iff₀ positiveSum]
  constructor <;> intro inequality <;> linarith

theorem dimensionRatio_lt_four_thirds_iff {massDimension resistanceDimension : ℝ}
    (positiveSum : 0 < massDimension + resistanceDimension) :
    dimensionRatio massDimension resistanceDimension < (4 / 3 : ℝ) ↔
      massDimension < 2 * resistanceDimension := by
  unfold dimensionRatio
  rw [div_lt_iff₀ positiveSum]
  constructor <;> intro inequality <;> linarith

theorem ao_equality_forces_open_rectangle {massDimension resistanceDimension : ℝ}
    (resistancePositive : 0 < resistanceDimension)
    (resistanceBelowOne : resistanceDimension < 1)
    (strictClock : 2 < massDimension + resistanceDimension)
    (aoEquality : dimensionRatio massDimension resistanceDimension = (4 / 3 : ℝ)) :
    (4 / 3 : ℝ) < massDimension ∧ massDimension < 2 ∧
      (2 / 3 : ℝ) < resistanceDimension ∧ resistanceDimension < 1 := by
  have equality := (dimensionRatio_eq_four_thirds_iff (by linarith)).mp aoEquality
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · exact resistanceBelowOne

theorem ao_inequality_outside_open_rectangle {massDimension resistanceDimension : ℝ}
    (resistancePositive : 0 < resistanceDimension)
    (resistanceBelowOne : resistanceDimension < 1)
    (strictClock : 2 < massDimension + resistanceDimension)
    (outside : ¬ ((4 / 3 : ℝ) < massDimension ∧ massDimension < 2 ∧
      (2 / 3 : ℝ) < resistanceDimension ∧ resistanceDimension < 1)) :
    dimensionRatio massDimension resistanceDimension ≠ (4 / 3 : ℝ) := by
  intro equality
  exact outside (ao_equality_forces_open_rectangle resistancePositive
    resistanceBelowOne strictClock equality)

theorem spectral_above_ao_of_mass_at_least_two {massDimension resistanceDimension : ℝ}
    (resistancePositive : 0 < resistanceDimension)
    (resistanceBelowOne : resistanceDimension < 1)
    (largeMass : 2 ≤ massDimension) :
    (4 / 3 : ℝ) < dimensionRatio massDimension resistanceDimension := by
  apply (dimensionRatio_gt_four_thirds_iff (by linarith)).mpr
  linarith

theorem spectral_below_ao_of_mass_at_most_four_thirds
    {massDimension resistanceDimension : ℝ}
    (strictClock : 2 < massDimension + resistanceDimension)
    (smallMass : massDimension ≤ (4 / 3 : ℝ)) :
    dimensionRatio massDimension resistanceDimension < (4 / 3 : ℝ) := by
  apply (dimensionRatio_lt_four_thirds_iff (by linarith)).mpr
  linarith

theorem chemicalResistanceDimension_pos {resistanceGrowth chemicalGrowth : ℝ}
    (resistanceSuperunit : 1 < resistanceGrowth)
    (chemicalSuperunit : 1 < chemicalGrowth) :
    0 < chemicalResistanceDimension resistanceGrowth chemicalGrowth :=
  div_pos (Real.log_pos resistanceSuperunit) (Real.log_pos chemicalSuperunit)

theorem chemicalResistanceDimension_lt_one {resistanceGrowth chemicalGrowth : ℝ}
    (resistancePositive : 0 < resistanceGrowth)
    (chemicalSuperunit : 1 < chemicalGrowth)
    (strictComparison : resistanceGrowth < chemicalGrowth) :
    chemicalResistanceDimension resistanceGrowth chemicalGrowth < 1 := by
  unfold chemicalResistanceDimension
  rw [div_lt_one (Real.log_pos chemicalSuperunit)]
  exact Real.log_lt_log resistancePositive strictComparison

theorem strict_clock_of_core_comparisons {massGrowth coreGrowth chemicalGrowth
    resistanceGrowth : ℝ}
    (resistancePositive : 0 < resistanceGrowth)
    (fullMassStrict : coreGrowth < massGrowth)
    (coreClock : chemicalGrowth ^ 2 ≤ coreGrowth * resistanceGrowth) :
    chemicalGrowth ^ 2 < massGrowth * resistanceGrowth := by
  exact coreClock.trans_lt (mul_lt_mul_of_pos_right fullMassStrict resistancePositive)

theorem strict_dimension_clock_of_growth_clock
    {massGrowth chemicalGrowth resistanceGrowth : ℝ}
    (massPositive : 0 < massGrowth)
    (resistancePositive : 0 < resistanceGrowth)
    (chemicalSuperunit : 1 < chemicalGrowth)
    (strictClock : chemicalGrowth ^ 2 < massGrowth * resistanceGrowth) :
    2 < chemicalMassDimension massGrowth chemicalGrowth +
      chemicalResistanceDimension resistanceGrowth chemicalGrowth := by
  have chemicalPositive : 0 < chemicalGrowth := lt_trans zero_lt_one chemicalSuperunit
  have logarithmicClock := Real.log_lt_log (sq_pos_of_pos chemicalPositive) strictClock
  rw [Real.log_pow, Real.log_mul (ne_of_gt massPositive)
    (ne_of_gt resistancePositive)] at logarithmicClock
  unfold chemicalMassDimension chemicalResistanceDimension
  rw [← add_div, lt_div_iff₀ (Real.log_pos chemicalSuperunit)]
  norm_num at logarithmicClock
  exact logarithmicClock

theorem typicalSpectralDimension_eq_dimensionRatio
    {massGrowth chemicalGrowth resistanceGrowth : ℝ}
    (massSuperunit : 1 < massGrowth)
    (resistanceSuperunit : 1 < resistanceGrowth)
    (chemicalSuperunit : 1 < chemicalGrowth) :
    typicalSpectralDimension massGrowth resistanceGrowth =
      dimensionRatio (chemicalMassDimension massGrowth chemicalGrowth)
        (chemicalResistanceDimension resistanceGrowth chemicalGrowth) := by
  have massPositive : 0 < massGrowth := lt_trans zero_lt_one massSuperunit
  have resistancePositive : 0 < resistanceGrowth := lt_trans zero_lt_one resistanceSuperunit
  have chemicalLogNonzero := ne_of_gt (Real.log_pos chemicalSuperunit)
  have sumLogNonzero : Real.log massGrowth + Real.log resistanceGrowth ≠ 0 :=
    ne_of_gt (add_pos (Real.log_pos massSuperunit) (Real.log_pos resistanceSuperunit))
  unfold typicalSpectralDimension dimensionRatio chemicalMassDimension
    chemicalResistanceDimension
  rw [Real.log_mul (ne_of_gt massPositive) (ne_of_gt resistancePositive), ← add_div]
  field_simp

theorem typicalSpectralDimension_eq_four_thirds_iff
    {massGrowth resistanceGrowth : ℝ}
    (massSuperunit : 1 < massGrowth)
    (resistanceSuperunit : 1 < resistanceGrowth) :
    typicalSpectralDimension massGrowth resistanceGrowth = (4 / 3 : ℝ) ↔
      massGrowth = resistanceGrowth ^ 2 := by
  have massPositive : 0 < massGrowth := lt_trans zero_lt_one massSuperunit
  have resistancePositive : 0 < resistanceGrowth := lt_trans zero_lt_one resistanceSuperunit
  have sumPositive := add_pos (Real.log_pos massSuperunit) (Real.log_pos resistanceSuperunit)
  have logarithmicEquivalence : typicalSpectralDimension massGrowth resistanceGrowth =
      (4 / 3 : ℝ) ↔ Real.log massGrowth = 2 * Real.log resistanceGrowth := by
    unfold typicalSpectralDimension
    rw [Real.log_mul (ne_of_gt massPositive) (ne_of_gt resistancePositive),
      div_eq_iff (ne_of_gt sumPositive)]
    constructor <;> intro equality <;> linarith
  rw [logarithmicEquivalence]
  constructor
  · intro equality
    calc
      massGrowth = Real.exp (Real.log massGrowth) := (Real.exp_log massPositive).symm
      _ = Real.exp (Real.log (resistanceGrowth ^ 2)) := by
        rw [Real.log_pow]
        norm_num
        rw [equality]
      _ = resistanceGrowth ^ 2 := Real.exp_log (sq_pos_of_pos resistancePositive)
  · intro equality
    rw [equality, Real.log_pow]
    norm_num

end

end IGSIII34
