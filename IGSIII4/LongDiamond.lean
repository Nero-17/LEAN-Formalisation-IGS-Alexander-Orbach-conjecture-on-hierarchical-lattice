import IGSIII4.LongDiamondPaths
import IGSIII4.AlexanderOrbach
import IGSIII.Chemical.EqualLengthScalar

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.LongDiamond
noncomputable section
open IGSIII34 IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall

theorem actual_chemical_factor_ten (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : network.reliability probability = probability)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    chemical.growth = 10 := by
  obtain ⟨constant, constantPositive, bounds⟩ := chemical.meanBounds
  apply IGSIII.Probability.exponential_growth_unique (manuscriptDistanceMean rule probability)
    chemical.growth 10 constant⁻¹ 1
    (zero_lt_one.trans (actual_chemical_growth_above_one rule classical probability positive belowOne fixedPoint chemical))
    (by norm_num) bounds
  intro depth
  rw [manuscript_mean_eq_pow_of_equal_paths rule classical 10 equal_terminal_path_lengths
    probability positive belowOne fixedPoint depth, one_mul]
  exact ⟨le_rfl, le_rfl⟩

theorem mass_growth_below_twenty (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1) :
    actualMassGrowth rule probability < 20 :=
  classical.mass_spectralRadius_lt_edges probability positive belowOne

theorem log_twenty_over_log_ten_lt_four_thirds :
    Real.log 20 / Real.log 10 < (4 / 3 : ℝ) := by
  have logarithmic := Real.log_lt_log (by norm_num : (0 : ℝ) < (20 : ℝ) ^ 3)
    (by norm_num : (20 : ℝ) ^ 3 < (10 : ℝ) ^ 4)
  rw [Real.log_pow, Real.log_pow] at logarithmic
  norm_num only [Nat.cast_ofNat] at logarithmic
  rw [div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 10))]
  linarith

theorem chemical_mass_dimension_bound (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : network.reliability probability = probability)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    chemicalMassDimension (actualMassGrowth rule probability) chemical.growth < Real.log 20 / Real.log 10 ∧
      Real.log 20 / Real.log 10 < (4 / 3 : ℝ) := by
  refine ⟨?_, log_twenty_over_log_ten_lt_four_thirds⟩
  rw [chemicalMassDimension, actual_chemical_factor_ten probability positive belowOne fixedPoint chemical]
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 10))
  exact Real.log_lt_log (zero_lt_one.trans (actualMassGrowth_above_one rule classical probability positive belowOne))
    (mass_growth_below_twenty probability positive belowOne)

theorem spectral_dimension_strictly_below_four_thirds (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule) :
    typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth < (4 / 3 : ℝ) := by
  obtain ⟨chemical⟩ := exists_actual_chemical_section_two rule classical probability positive belowOne fixedPoint
  apply actual_spectral_below_ao_of_mass_at_most_four_thirds rule classical probability positive belowOne fixedPoint
    accepted upper pruning chemical
  obtain ⟨first, second⟩ := chemical_mass_dimension_bound probability positive belowOne fixedPoint chemical
  exact (first.trans second).le

end
end IGSIII4.LongDiamond
