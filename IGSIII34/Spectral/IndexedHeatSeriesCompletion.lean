import IGSIII34.Spectral.IndexedWeightedSeriesCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The uniform heat-series construction from continuous eigenfunctions,
diverging nonnegative eigenvalues and the bounded evaluation estimate.
Obtaining these spectral data from the actual resistance form remains separate.
-/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open Filter Set
open scoped Topology
variable {Index : Type*}

theorem indexed_exponential_spectral_weight_tendsto_zero_completion
    (eigenvalues : Index → ℝ) (diverge : Tendsto eigenvalues cofinite atTop)
    (time : ℝ) (positive : 0 < time) :
    Tendsto (fun index => (1 + eigenvalues index) * Real.exp (-time * eigenvalues index))
      cofinite (𝓝 0) := by
  have constantPart := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 time positive).comp diverge
  have linearPart := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 time positive).comp diverge
  simp only [Real.rpow_zero, one_mul] at constantPart
  simp only [Real.rpow_one] at linearPart
  convert constantPart.add linearPart using 1 <;> simp only [add_mul, one_mul, add_zero, Function.comp_def]

theorem indexed_spectral_term_norm_bound_completion
    (eigenvalue time initial first second : ℝ)
    (eigenvalueNonnegative : 0 ≤ eigenvalue) (timeBound : initial ≤ time) :
    ‖Real.exp (-time * eigenvalue) * first * second‖ ≤
      ((1 + eigenvalue) * Real.exp (-initial * eigenvalue)) *
        ((first ^ 2 / (1 + eigenvalue) + second ^ 2 / (1 + eigenvalue)) / 2) := by
  have denominatorPositive : 0 < 1 + eigenvalue := by linarith
  have exponentialBound : Real.exp (-time * eigenvalue) ≤ Real.exp (-initial * eigenvalue) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have productBound : |first| * |second| ≤ (first ^ 2 + second ^ 2) / 2 := by
    nlinarith [sq_nonneg (|first| - |second|), sq_abs first, sq_abs second]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-initial * eigenvalue) * (|first| * |second|) := by
      nlinarith [mul_le_mul_of_nonneg_right exponentialBound
        (mul_nonneg (abs_nonneg first) (abs_nonneg second))]
    _ ≤ Real.exp (-initial * eigenvalue) * ((first ^ 2 + second ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left productBound (Real.exp_pos _).le
    _ = _ := by field_simp

def indexedSpectralHeatKernelCompletion {Space : Type*} (eigenvalues : Index → ℝ)
    (eigenfunctions : Index → Space → ℝ) (time : ℝ) (first second : Space) : ℝ :=
  ∑' index, Real.exp (-time * eigenvalues index) * eigenfunctions index first * eigenfunctions index second

theorem indexed_spectral_heat_series_uniform_completion
    {Space : Type*} (eigenvalues : Index → ℝ) (eigenfunctions : Index → Space → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound)
    (initial : ℝ) (initialPositive : 0 < initial) :
    TendstoUniformlyOn
      (fun depth (point : ℝ × Space × Space) => ∑ index ∈ depth,
        Real.exp (-point.1 * eigenvalues index) * eigenfunctions index point.2.1 * eigenfunctions index point.2.2)
      (fun point => indexedSpectralHeatKernelCompletion eigenvalues eigenfunctions point.1 point.2.1 point.2.2)
      atTop {point | initial ≤ point.1} := by
  have weightsNonnegative : ∀ index point,
      0 ≤ eigenfunctions index point ^ 2 / (1 + eigenvalues index) := by
    intro index point
    exact div_nonneg (sq_nonneg _) (by linarith [nonnegative index])
  have weightsSummable : ∀ point, Summable
      (fun index => eigenfunctions index point ^ 2 / (1 + eigenvalues index)) :=
    fun point => summable_of_sum_le (fun index => weightsNonnegative index point) (evaluation point)
  have weightsBound : ∀ point,
      (∑' index, eigenfunctions index point ^ 2 / (1 + eigenvalues index)) ≤ bound :=
    fun point => (weightsSummable point).tsum_le_of_sum_le (evaluation point)
  apply indexed_uniformly_tsum_of_weighted_tail_completion _
    (fun index point =>
      ((eigenfunctions index point.2.1 ^ 2 / (1 + eigenvalues index) +
        eigenfunctions index point.2.2 ^ 2 / (1 + eigenvalues index)) / 2))
    _ bound boundNonnegative
  · intro index point
    exact div_nonneg (add_nonneg (weightsNonnegative index point.2.1)
      (weightsNonnegative index point.2.2)) (by norm_num)
  · intro point _
    exact ((weightsSummable point.2.1).add (weightsSummable point.2.2)).div_const 2
  · intro point _
    rw [tsum_div_const, (weightsSummable point.2.1).tsum_add (weightsSummable point.2.2)]
    linarith [weightsBound point.2.1, weightsBound point.2.2]
  · intro tolerance positive
    filter_upwards [((indexed_exponential_spectral_weight_tendsto_zero_completion eigenvalues diverge initial initialPositive).eventually
      (gt_mem_nhds positive))] with index small point membership
    exact (indexed_spectral_term_norm_bound_completion _ _ _ _ _ (nonnegative index) membership).trans
      (mul_le_mul_of_nonneg_right small.le (div_nonneg
        (add_nonneg (weightsNonnegative index point.2.1) (weightsNonnegative index point.2.2))
        (by norm_num)))

theorem indexed_spectral_heat_kernel_continuousOn_completion
    {Space : Type*} [TopologicalSpace Space]
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → Space → ℝ)
    (eigenfunctionsContinuous : ∀ index, Continuous (eigenfunctions index))
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound) :
    ContinuousOn (fun point : ℝ × Space × Space =>
      indexedSpectralHeatKernelCompletion eigenvalues eigenfunctions point.1 point.2.1 point.2.2)
      {point | 0 < point.1} := by
  intro point positive
  have initialPositive : 0 < point.1 / 2 := half_pos positive
  have uniform := indexed_spectral_heat_series_uniform_completion eigenvalues eigenfunctions nonnegative diverge
    bound boundNonnegative evaluation (point.1 / 2) initialPositive
  have partialContinuous : ∀ depth, Continuous (fun other : ℝ × Space × Space =>
      ∑ index ∈ depth, Real.exp (-other.1 * eigenvalues index) *
        eigenfunctions index other.2.1 * eigenfunctions index other.2.2) := by
    intro depth
    apply continuous_finsetSum
    intro index _
    exact ((Real.continuous_exp.comp (continuous_fst.neg.mul continuous_const)).mul
      ((eigenfunctionsContinuous index).comp (continuous_fst.comp continuous_snd))).mul
      ((eigenfunctionsContinuous index).comp (continuous_snd.comp continuous_snd))
  have continuousOn := uniform.continuousOn
    (Frequently.of_forall (fun depth => (partialContinuous depth).continuousOn))
  have neighborhood : {other : ℝ × Space × Space | point.1 / 2 ≤ other.1} ∈ 𝓝 point := by
    apply mem_of_superset ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (show point.1 / 2 < point.1 by linarith))
    intro other membership
    change point.1 / 2 < other.1 at membership
    exact membership.le
  exact ((continuousOn point (by dsimp; linarith)).continuousAt neighborhood).continuousWithinAt

end
end IGSIII34.Spectral

