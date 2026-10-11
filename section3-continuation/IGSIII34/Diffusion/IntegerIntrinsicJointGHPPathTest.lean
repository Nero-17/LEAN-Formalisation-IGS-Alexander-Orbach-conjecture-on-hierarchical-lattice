import IGSIII34.Diffusion.IntrinsicJointGHPPathTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology BigOperators BoundedContinuousFunction NNReal ENNReal

/-- Integer-horizon joint tests allow a determining family for the genuine
joint metric. Global usual continuity is not assumed; the continuous-limit
transfer to usual-local J1 must be proved separately. -/
structure IntegerIntrinsicJointGHPPathTest where
  bound : ℝ≥0
  spatialLipschitz : ℝ≥0
  value : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space],
    JointMeasuredMarkedState Space → (SkorokhodCadlagPathCompletion20261011 Space →ᵇ ℝ)
  bounded : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (state : JointMeasuredMarkedState Space),
    ‖value Space state‖ ≤ bound
  spatialStability : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (first last : JointMeasuredMarkedState Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space),
    |value Space first path - value Space last path| ≤
      spatialLipschitz * jointMeasuredMarkedStateCost first last
  isometricTransport : ∀ (First Last : Type) [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First] [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last] (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First) (path : SkorokhodCadlagPathCompletion20261011 First),
    value Last (jointMeasuredMarkedStateMap mapping isometry.continuous state)
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path) =
      value First state path


def IntrinsicJointGHPPathTest.toInteger (test : IntrinsicJointGHPPathTest) :
    IntegerIntrinsicJointGHPPathTest where
  bound := test.bound
  spatialLipschitz := test.spatialLipschitz
  value := test.value
  bounded := test.bounded
  spatialStability := test.spatialStability
  isometricTransport := test.isometricTransport

theorem integer_intrinsic_joint_test_response_tendsto
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (test : IntegerIntrinsicJointGHPPathTest)
    (states : ℕ → JointMeasuredMarkedState Space) (state : JointMeasuredMarkedState Space)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (spatial : Tendsto (fun depth => jointMeasuredMarkedStateCost (states depth) state) atTop (𝓝 0))
    (weak : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun depth => ∫ path, test.value Space (states depth) path ∂(laws depth : Measure _)) atTop
      (𝓝 (∫ path, test.value Space state path ∂(law : Measure _))) := by
  have fixed := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weak (test.value Space state)
  have errorBound (depth : ℕ) :
      ‖(∫ path, test.value Space (states depth) path ∂(laws depth : Measure _)) -
        (∫ path, test.value Space state path ∂(laws depth : Measure _))‖ ≤
        test.spatialLipschitz * jointMeasuredMarkedStateCost (states depth) state := by
    rw [← integral_sub ((test.value Space (states depth)).integrable (μ := (laws depth : Measure _))) ((test.value Space state).integrable (μ := (laws depth : Measure _)))]
    simpa using norm_integral_le_of_norm_le_const (μ := (laws depth : Measure _))
      (f := fun path => test.value Space (states depth) path - test.value Space state path)
      (C := (test.spatialLipschitz : ℝ) * jointMeasuredMarkedStateCost (states depth) state)
      (Eventually.of_forall (fun path => by
        simpa only [Real.norm_eq_abs] using test.spatialStability Space (states depth) state path))
  have errorZero : Tendsto (fun depth =>
      (∫ path, test.value Space (states depth) path ∂(laws depth : Measure _)) -
        (∫ path, test.value Space state path ∂(laws depth : Measure _))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) errorBound
    simpa only [mul_zero] using spatial.const_mul (test.spatialLipschitz : ℝ)
  simpa only [sub_add_cancel, zero_add] using errorZero.add fixed


end
end IGSIII34.Diffusion
