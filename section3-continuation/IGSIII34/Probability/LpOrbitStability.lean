import IGSIII.Probability.Lp2Mean
import IGSIII.Probability.OmegaOrbit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem lp2_absolute_difference_mean_continuous
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (reference : Lp ℝ 2 measure) :
    Continuous (fun value : Lp ℝ 2 measure => ∫ sample, |value sample-reference sample| ∂measure) := by
  have equality (value : Lp ℝ 2 measure) : (∫ sample, |value sample-reference sample| ∂measure) =
      ∫ sample, (|value-reference| : Lp ℝ 2 measure) sample ∂measure := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_abs (value-reference), Lp.coeFn_sub value reference] with sample absolute subtraction
    rw [absolute, subtraction, Pi.sub_apply]
  simp_rw [equality]
  have differenceContinuous : Continuous (fun value : Lp ℝ 2 measure => value-reference) := continuous_id.sub continuous_const
  have absoluteContinuous : Continuous (fun value : Lp ℝ 2 measure => |value-reference|) := by
    change Continuous (fun value : Lp ℝ 2 measure => (value-reference) ⊔ -(value-reference))
    exact differenceContinuous.sup differenceContinuous.neg
  exact (IGSIII.Probability.lp2_mean_continuous measure).comp absoluteContinuous

theorem lp2_orbit_cluster_eq_of_vanishing_eventual_mean_error
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (reference : Lp ℝ 2 measure)
    (error : ℕ → ℝ) (errorTendstoZero : Tendsto error atTop (𝓝 0))
    (estimates : ∀ block, ∀ᶠ depth : ℕ in atTop,
      (∫ sample, |sequence depth sample-reference sample| ∂measure) ≤ error block)
    (point : Lp ℝ 2 measure) (cluster : MapClusterPt point atTop sequence) : point = reference := by
  have meanBound (block : ℕ) : (∫ sample, |point sample-reference sample| ∂measure) ≤ error block := by
    apply (isClosed_Iic : IsClosed (Set.Iic (error block))).mem_of_mapClusterPt
      (cluster.continuousAt_comp (lp2_absolute_difference_mean_continuous measure reference).continuousAt)
    exact estimates block
  have zeroIntegral : (∫ sample, |point sample-reference sample| ∂measure) = 0 :=
    le_antisymm (ge_of_tendsto' errorTendstoZero meanBound) (integral_nonneg (fun _ => abs_nonneg _))
  have integrable : Integrable (fun sample => |point sample-reference sample|) measure :=
    (((Lp.memLp point).sub (Lp.memLp reference)).integrable (by norm_num)).abs
  have zeroAe := (integral_eq_zero_iff_of_nonneg (fun sample => abs_nonneg (point sample-reference sample)) integrable).mp zeroIntegral
  apply Lp.ext
  filter_upwards [zeroAe] with sample equality
  exact sub_eq_zero.mp (abs_eq_zero.mp equality)

theorem lp2_orbit_tendsto_of_compact_and_vanishing_eventual_mean_error
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (precompact : IsCompact (closure (Set.range sequence)))
    (reference : Lp ℝ 2 measure) (error : ℕ → ℝ) (errorTendstoZero : Tendsto error atTop (𝓝 0))
    (estimates : ∀ block, ∀ᶠ depth : ℕ in atTop,
      (∫ sample, |sequence depth sample-reference sample| ∂measure) ≤ error block) :
    Tendsto sequence atTop (𝓝 reference) := by
  apply precompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun depth => subset_closure ⟨depth, rfl⟩))
  intro point _ cluster
  exact lp2_orbit_cluster_eq_of_vanishing_eventual_mean_error measure sequence reference error errorTendstoZero estimates point cluster

end
end IGSIII34.Probability


