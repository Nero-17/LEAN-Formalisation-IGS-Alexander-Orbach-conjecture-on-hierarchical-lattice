import IGSIII.Chemical.SmallBall.ChemicalOrbitConvergence
import IGSIII.Chemical.AddressConvergence
import IGSIII.Chemical.ChemicalMeanLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter IGSIII.Geometry IGSIII.Chemical.SmallBall
open scoped ENNReal Topology

theorem exists_actual_chemical_scalar
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        ∃ amplitude : ℝ, 1 ≤ amplitude ∧
          (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
            0 < chemicalField rule p positive belowOne fixedPoint value address marks ∧
            (edgePathFamily rule.network (marks (address, true))).shortest
              (fun edge => chemicalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
                growth * chemicalField rule p positive belowOne fixedPoint value address marks ∧
            Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
              atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) ∧
          (∀ order : ℝ≥0∞, order ≠ 0 → order ≠ ∞ → ∀ address,
            Tendsto (fun depth => eLpNorm
              (fun marks => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) -
                amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)
              order (independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0)) ∧
          Tendsto (fun depth => manuscriptDistanceMean rule p depth / growth ^ depth) atTop (𝓝 amplitude) ∧
          (∀ order : ℝ≥0∞, order ≠ 0 → order ≠ ∞ →
            MemLp value order (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
            MemLp (fun marks => (value marks)⁻¹) order (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
          (∀ parameter : ℝ, 0 ≤ parameter →
            (∫⁻ marks, ENNReal.ofReal (Real.exp (parameter * value marks))
              ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    value, valueFixed, valuePositive, valueMeanOne, lower, upper, lowerPositive, upperPositive, comparison,
    amplitude, amplitudeAtLeastOne, _, _, convergence⟩ :=
    exists_actual_chemical_orbit_convergence rule classical p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower
  have lpConvergence (order : ℝ≥0∞) (orderPositive : order ≠ 0) (orderFinite : order ≠ ∞) :=
    chemicalOrbit_all_finite_lp_of_ae_tendsto rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive meanBounds value valueFixed valuePositive
      lower upper lowerPositive upperPositive comparison (amplitude • value) convergence order orderPositive orderFinite
  have moments := chemical_value_all_finite_lp_of_omega_comparison_bounds rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds value valuePositive
    lower upper lowerPositive upperPositive comparison
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    value, valueFixed, valuePositive, valueMeanOne, amplitude, amplitudeAtLeastOne, ?_, ?_, ?_, moments.1, moments.2⟩
  · filter_upwards [chemicalField_positive rule p positive belowOne fixedPoint value valuePositive,
      chemicalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valueFixed,
      chemical_terminal_field_ae_convergence_of_orbit_convergence rule classical p positive belowOne fixedPoint
        growth growthPositive value amplitude convergence] with marks positivity stationary limits
    exact fun address => ⟨positivity address, stationary address, limits address⟩
  · intro order orderPositive orderFinite address
    exact chemical_terminal_field_lp_convergence_of_orbit_convergence rule classical p positive belowOne fixedPoint
      growth growthPositive value amplitude order (lpConvergence order orderPositive orderFinite).2.2 address
  · exact chemical_mean_ratio_tendsto_of_l1_convergence rule classical p positive belowOne fixedPoint growth growthPositive.le
      value valueMeanOne amplitude (lpConvergence 1 (by norm_num) (by norm_num)).2.2

end IGSIII.Chemical.Substitution
