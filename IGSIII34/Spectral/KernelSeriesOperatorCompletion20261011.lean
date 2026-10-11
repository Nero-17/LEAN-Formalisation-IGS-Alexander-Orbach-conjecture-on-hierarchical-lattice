import IGSIII34.Spectral.ContinuousKernelOperatorCompletion20261011
import IGSIII34.Spectral.IndexedHeatSeriesCompletion20261011
import IGSIII34.Spectral.FormSemigroupIntertwiningCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped Topology NNReal

variable {Space Index : Type*} [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [MeasurableSpace Space] [BorelSpace Space] (measure : Measure Space) [IsProbabilityMeasure measure]

theorem spectral_kernel_row_hasSum_continuous_completion20261011
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → C(Space, ℝ))
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound)
    (time : ℝ) (timePositive : 0 < time) (kernel : C(Space × Space, ℝ))
    (kernelIdentity : ∀ first second, kernel (first, second) =
      indexedSpectralHeatKernelCompletion20261011 eigenvalues (fun index => eigenfunctions index)
        time first second) (point : Space) :
    HasSum (fun index => (Real.exp (-time * eigenvalues index) * eigenfunctions index point) •
      eigenfunctions index) (kernel.curry point) := by
  classical
  have uniform := indexed_spectral_heat_series_uniform_completion20261011 eigenvalues
    (fun index => eigenfunctions index) nonnegative diverge bound boundNonnegative evaluation time timePositive
  have convergence : Tendsto (fun indices : Finset Index =>
      ∑ index ∈ indices, (Real.exp (-time * eigenvalues index) * eigenfunctions index point) •
        eigenfunctions index) atTop (𝓝 (kernel.curry point)) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp uniform)
      (tolerance / 2) (half_pos positive)] with indices small
    rw [dist_eq_norm, norm_sub_rev]
    apply lt_of_le_of_lt _ (half_lt_self positive)
    apply (ContinuousMap.norm_le _ (half_pos positive).le).mpr
    intro other
    have estimate := (small (time, point, other) (by simp)).le
    simpa only [dist_eq_norm, kernelIdentity, ContinuousMap.curry_apply,
      ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul] using estimate
  simpa only [HasSum, SummationFilter.unconditional_filter] using convergence

theorem spectral_kernel_row_hasSum_l2_completion20261011
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → C(Space, ℝ))
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound)
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure))
    (basisImage : ∀ index, ContinuousMap.toLp 2 measure ℝ (eigenfunctions index) = basis index)
    (time : ℝ) (timePositive : 0 < time) (kernel : C(Space × Space, ℝ))
    (kernelIdentity : ∀ first second, kernel (first, second) =
      indexedSpectralHeatKernelCompletion20261011 eigenvalues (fun index => eigenfunctions index)
        time first second) (point : Space) :
    HasSum (fun index => (Real.exp (-time * eigenvalues index) * eigenfunctions index point) •
      basis index) (ContinuousMap.toLp 2 measure ℝ (kernel.curry point)) := by
  have sum := (spectral_kernel_row_hasSum_continuous_completion20261011 eigenvalues eigenfunctions
    nonnegative diverge bound boundNonnegative evaluation time timePositive kernel kernelIdentity point).mapL
      (ContinuousMap.toLp 2 measure ℝ)
  simpa only [map_smul, basisImage] using sum

theorem spectral_kernel_operator_basis_completion20261011
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → C(Space, ℝ))
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound)
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure))
    (basisImage : ∀ index, ContinuousMap.toLp 2 measure ℝ (eigenfunctions index) = basis index)
    (time : ℝ) (timePositive : 0 < time) (kernel : C(Space × Space, ℝ))
    (kernelIdentity : ∀ first second, kernel (first, second) =
      indexedSpectralHeatKernelCompletion20261011 eigenvalues (fun index => eigenfunctions index)
        time first second) (index : Index) :
    continuousKernelL2OperatorCompletion20261011 measure kernel (basis index) =
      Real.exp (-time * eigenvalues index) • eigenfunctions index := by
  classical
  ext point
  have rowSum := spectral_kernel_row_hasSum_l2_completion20261011 measure eigenvalues eigenfunctions
    nonnegative diverge bound boundNonnegative evaluation basis basisImage time timePositive kernel kernelIdentity point
  have innerSum := rowSum.mapL (innerSL ℝ (basis index))
  have reduced : HasSum (fun other : Index => if other = index then
      Real.exp (-time * eigenvalues index) * eigenfunctions index point else 0)
      (inner ℝ (basis index) (ContinuousMap.toLp 2 measure ℝ (kernel.curry point))) := by
    convert! innerSum using 1
    funext other
    simp only [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.mp basis.orthonormal]
    by_cases equal : other = index
    · subst other
      simp
    · simp [equal, Ne.symm equal]
  have value := reduced.unique (hasSum_ite_eq index
    (Real.exp (-time * eigenvalues index) * eigenfunctions index point))
  change inner ℝ (ContinuousMap.toLp 2 measure ℝ (kernel.curry point)) (basis index) = _
  rw [real_inner_comm]
  exact value

theorem spectral_kernel_operator_identification_completion20261011
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → C(Space, ℝ))
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (evaluation : ∀ point, ∀ indices : Finset Index,
      ∑ index ∈ indices, eigenfunctions index point ^ 2 / (1 + eigenvalues index) ≤ bound)
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure))
    (basisImage : ∀ index, ContinuousMap.toLp 2 measure ℝ (eigenfunctions index) = basis index)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) (kernel : C(Space × Space, ℝ))
    (kernelIdentity : ∀ first second, kernel (first, second) =
      indexedSpectralHeatKernelCompletion20261011 eigenvalues (fun index => eigenfunctions index)
        time first second) :
    (ContinuousMap.toLp 2 measure ℝ).comp (continuousKernelL2OperatorCompletion20261011 measure kernel) =
      spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time := by
  apply continuousLinearMap_eq_on_hilbert_basis_target_completion20261011 basis
  intro index
  simp only [ContinuousLinearMap.comp_apply,
    spectral_kernel_operator_basis_completion20261011 measure eigenvalues eigenfunctions nonnegative diverge
      bound boundNonnegative evaluation basis basisImage time timePositive kernel kernelIdentity,
    map_smul, basisImage, spectralL2Semigroup_basis_completion20261011]

end
end IGSIII34.Spectral

