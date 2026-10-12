import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] (measure : Measure Space)
  [IsProbabilityMeasure measure] [measure.IsOpenPosMeasure]

theorem continuousMap_le_iff_toLp_le_completion (first second : C(Space, ℝ)) :
    (∀ point, first point ≤ second point) ↔
      ContinuousMap.toLp 2 measure ℝ first ≤ ContinuousMap.toLp 2 measure ℝ second := by
  have firstRepresentative := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure first
  have secondRepresentative := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure second
  constructor
  · intro pointwise
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [firstRepresentative, secondRepresentative] with point firstAt secondAt
    rw [firstAt, secondAt]
    exact pointwise point
  · intro order
    have almostEverywhere : ∀ᵐ point ∂measure, first point ≤ second point := by
      filter_upwards [(Lp.coeFn_le _ _).mpr order, firstRepresentative, secondRepresentative] with point pointOrder firstAt secondAt
      rwa [firstAt, secondAt] at pointOrder
    have closed : IsClosed {point | first point ≤ second point} := isClosed_le first.continuous second.continuous
    have all : closure {point | first point ≤ second point} = Set.univ := (measure.dense_of_ae almostEverywhere).closure_eq
    intro point
    apply closure_minimal (Set.Subset.refl _) closed
    rw [all]
    trivial

theorem continuousMap_nonnegative_of_toLp_nonnegative_completion (function : C(Space, ℝ))
    (nonnegative : 0 ≤ ContinuousMap.toLp 2 measure ℝ function) : ∀ point, 0 ≤ function point := by
  have order : ContinuousMap.toLp 2 measure ℝ (0 : C(Space, ℝ)) ≤ ContinuousMap.toLp 2 measure ℝ function := by simpa only [map_zero] using nonnegative
  exact (continuousMap_le_iff_toLp_le_completion measure 0 function).mpr order

theorem continuousMap_operator_norm_bound_completion
    (operator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (positive : ∀ forcing, 0 ≤ forcing → 0 ≤ operator forcing)
    (constants : ∀ constant, operator (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space constant)) =
      ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space constant))
    (first second : C(Space, ℝ))
    (representation : ContinuousMap.toLp 2 measure ℝ second = operator (ContinuousMap.toLp 2 measure ℝ first)) :
    ‖second‖ ≤ ‖first‖ := by
  have firstUpper : ContinuousMap.toLp 2 measure ℝ first ≤
      ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space ‖first‖) :=
    (continuousMap_le_iff_toLp_le_completion measure _ _).mp
      (fun point => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, ContinuousMap.const_apply] using ContinuousMap.norm_coe_le_norm first point))
  have firstLower : ContinuousMap.toLp 2 measure ℝ (-first) ≤
      ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space ‖first‖) :=
    (continuousMap_le_iff_toLp_le_completion measure _ _).mp
      (fun point => (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs, ContinuousMap.const_apply] using ContinuousMap.norm_coe_le_norm first point))
  have secondUpper := positive _ (sub_nonneg.mpr firstUpper)
  rw [map_sub, constants, ← representation] at secondUpper
  have secondLower := positive _ (sub_nonneg.mpr firstLower)
  rw [map_sub, constants, map_neg, map_neg, ← representation, ← map_neg] at secondLower
  have upper := (continuousMap_le_iff_toLp_le_completion measure second (ContinuousMap.const Space ‖first‖)).mpr (sub_nonneg.mp secondUpper)
  have lower := (continuousMap_le_iff_toLp_le_completion measure (-second) (ContinuousMap.const Space ‖first‖)).mpr (sub_nonneg.mp secondLower)
  apply (ContinuousMap.norm_le _ (norm_nonneg first)).mpr
  intro point
  exact abs_le.mpr ⟨by simpa only [ContinuousMap.neg_apply, ContinuousMap.const_apply, neg_neg] using neg_le_neg (lower point), upper point⟩

end
end IGSIII34.Spectral


