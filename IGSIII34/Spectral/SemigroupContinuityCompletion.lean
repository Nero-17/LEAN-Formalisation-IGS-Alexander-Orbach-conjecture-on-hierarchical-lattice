import IGSIII34.Spectral.DiagonalSemigroupCompletion
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology NNReal

variable {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

theorem spectralL2Semigroup_continuous_completion
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (value : Hilbert) :
    Continuous (fun time : ℝ≥0 => spectralL2SemigroupCompletion basis eigenvalues nonnegative time value) := by
  classical
  have approximate : TendstoUniformly
      (fun indices : Finset Index => fun time : ℝ≥0 =>
        spectralL2SemigroupCompletion basis eigenvalues nonnegative time
          (∑ index ∈ indices, basis.repr value index • basis index))
      (fun time : ℝ≥0 => spectralL2SemigroupCompletion basis eigenvalues nonnegative time value) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon positive
    have eventual : ∀ᶠ indices : Finset Index in atTop,
        dist value (∑ index ∈ indices, basis.repr value index • basis index) < epsilon := by
      simpa only [SummationFilter.unconditional_filter, dist_comm] using (basis.hasSum_repr value).eventually (Metric.ball_mem_nhds value positive)
    filter_upwards [eventual] with indices bound time
    rw [dist_eq_norm, ← map_sub]
    exact (spectralL2Semigroup_norm_le_completion basis eigenvalues nonnegative time _).trans_lt
      (by simpa only [dist_eq_norm] using bound)
  apply approximate.continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro indices
  have continuousSum : Continuous (fun time : ℝ≥0 =>
      ∑ index ∈ indices, (basis.repr value index * Real.exp (-(time : ℝ) * eigenvalues index)) • basis index) := by
    apply continuous_finsetSum
    intro index membership
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_subtype_val.neg.mul continuous_const))).smul continuous_const
  simpa only [map_sum, map_smul, spectralL2Semigroup_basis_completion, smul_smul] using continuousSum

end
end IGSIII34.Spectral
