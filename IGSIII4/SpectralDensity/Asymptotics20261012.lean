import IGSIII34.AO.Dimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp

/-! Analytic finishing steps for the spectral-density construction.
These lemmas are explicitly conditional on logarithmic growth estimates.
The actual finite-rule construction must discharge those estimates before
the manuscript's spectral-density theorem can be claimed. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology IGSIII34

def limitingDimension (base : ℝ) : ℝ :=
  2 * (Real.log base + Real.log (4 / 3 : ℝ)) /
    (2 * Real.log base + Real.log (4 / 3 : ℝ))

theorem spectral_limit_of_normalized_log_growth
    (massGrowth resistanceGrowth : ℕ → ℝ) (massRate resistanceRate : ℝ)
    (massPositive : ∀ depth, 0 < massGrowth depth)
    (resistancePositive : ∀ depth, 0 < resistanceGrowth depth)
    (massLimit : Tendsto (fun depth => Real.log (massGrowth depth) / (depth : ℝ))
      atTop (𝓝 massRate))
    (resistanceLimit : Tendsto (fun depth => Real.log (resistanceGrowth depth) / (depth : ℝ))
      atTop (𝓝 resistanceRate))
    (sumNonzero : massRate + resistanceRate ≠ 0) :
    Tendsto (fun depth => typicalSpectralDimension (massGrowth depth) (resistanceGrowth depth))
      atTop (𝓝 (2 * massRate / (massRate + resistanceRate))) := by
  have quotientLimit := (massLimit.const_mul 2).div (massLimit.add resistanceLimit) sumNonzero
  apply quotientLimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with depth depthPositive
  have depthNonzero : (depth : ℝ) ≠ 0 := by exact_mod_cast (by omega : depth ≠ 0)
  change (2 * (Real.log (massGrowth depth) / (depth : ℝ))) /
    (Real.log (massGrowth depth) / (depth : ℝ) + Real.log (resistanceGrowth depth) / (depth : ℝ)) =
    typicalSpectralDimension (massGrowth depth) (resistanceGrowth depth)
  simp only [typicalSpectralDimension,
    Real.log_mul (ne_of_gt (massPositive depth)) (ne_of_gt (resistancePositive depth))]
  field_simp

theorem limitingDimension_mem_Ioo (base : ℝ) (baseAboveOne : 1 < base) :
    limitingDimension base ∈ Set.Ioo (1 : ℝ) 2 := by
  have baseLogPositive := Real.log_pos baseAboveOne
  have fixedLogPositive : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have denominatorPositive : 0 < 2 * Real.log base + Real.log (4 / 3 : ℝ) := by positivity
  constructor
  · rw [limitingDimension, lt_div_iff₀ denominatorPositive]
    linarith
  · rw [limitingDimension, div_lt_iff₀ denominatorPositive]
    linarith

theorem limitingDimension_surjective_Ioo (dimension : ℝ)
    (dimensionAboveOne : 1 < dimension) (dimensionBelowTwo : dimension < 2) :
    ∃ base : ℝ, 1 < base ∧ limitingDimension base = dimension := by
  refine ⟨Real.exp (Real.log (4 / 3 : ℝ) * (2 - dimension) / (2 * (dimension - 1))), ?_, ?_⟩
  · have exponentPositive : 0 < Real.log (4 / 3 : ℝ) * (2 - dimension) / (2 * (dimension - 1)) :=
      div_pos (mul_pos (Real.log_pos (by norm_num)) (by linarith)) (by linarith)
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr exponentPositive
  · have dimensionNonzero : dimension - 1 ≠ 0 := ne_of_gt (by linarith)
    have fixedLogNonzero : Real.log (4 / 3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    simp only [limitingDimension, Real.log_exp]
    field_simp
    <;> ring

theorem spectral_limit_of_density_growth_rates
    (base : ℝ) (baseAboveOne : 1 < base)
    (massGrowth resistanceGrowth : ℕ → ℝ)
    (massPositive : ∀ depth, 0 < massGrowth depth)
    (resistancePositive : ∀ depth, 0 < resistanceGrowth depth)
    (massLimit : Tendsto (fun depth => Real.log (massGrowth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base + Real.log (4 / 3 : ℝ))))
    (resistanceLimit : Tendsto (fun depth => Real.log (resistanceGrowth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base))) :
    Tendsto (fun depth => typicalSpectralDimension (massGrowth depth) (resistanceGrowth depth))
      atTop (𝓝 (limitingDimension base)) := by
  have denominatorPositive : 0 < (Real.log base + Real.log (4 / 3 : ℝ)) + Real.log base := by
    have := Real.log_pos baseAboveOne
    have : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
    positivity
  convert spectral_limit_of_normalized_log_growth massGrowth resistanceGrowth
    (Real.log base + Real.log (4 / 3 : ℝ)) (Real.log base)
    massPositive resistancePositive massLimit resistanceLimit (ne_of_gt denominatorPositive) using 1
  simp only [limitingDimension]
  congr 1
  ring

theorem intervals_hit_of_limitingDimension_limits
    (dimensions : Set ℝ)
    (approximation : ∀ base : ℝ, 1 < base → ∃ sequence : ℕ → ℝ,
      (∀ depth, sequence depth ∈ dimensions) ∧
      Tendsto sequence atTop (𝓝 (limitingDimension base)))
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ dimension ∈ dimensions, dimension ∈ Set.Ioo lower upper := by
  obtain ⟨base, baseAboveOne, baseValue⟩ := limitingDimension_surjective_Ioo
    ((lower + upper) / 2) (by linarith) (by linarith)
  obtain ⟨sequence, sequenceMember, sequenceLimit⟩ := approximation base baseAboveOne
  have inInterval : Set.Ioo lower upper ∈ 𝓝 (limitingDimension base) := by
    rw [baseValue]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨depth, depthGood⟩ := (sequenceLimit.eventually inInterval).exists
  exact ⟨sequence depth, sequenceMember depth, depthGood⟩

end
end IGSIII4.SpectralDensity
