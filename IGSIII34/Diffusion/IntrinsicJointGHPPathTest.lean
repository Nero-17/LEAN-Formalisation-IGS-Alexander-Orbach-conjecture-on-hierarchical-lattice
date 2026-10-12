import IGSIII34.Diffusion.UsualLocalJ1WeakTests
import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion
import IGSIII34.Spectral.Collars.MeasureTransport
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology BigOperators BoundedContinuousFunction NNReal ENNReal

def JointMeasuredMarkedState (Space : Type*) [TopologicalSpace Space] [MeasurableSpace Space] :=
  NonemptyCompacts Space × (Bool → Space) × (Bool → ProbabilityMeasure Space)

def jointMeasuredMarkedStateCost {Space : Type*} [MetricSpace Space]
    [MeasurableSpace Space] (first last : JointMeasuredMarkedState Space) : ℝ :=
  dist first.1 last.1 + ∑ side : Bool, dist (first.2.1 side) (last.2.1 side) +
    ∑ side : Bool, levyProkhorovDist (first.2.2 side : Measure Space) (last.2.2 side : Measure Space)

def jointMeasuredMarkedStateMap {First Last : Type*} [MetricSpace First] [MetricSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (mapping : First → Last) (continuous : Continuous mapping)
    (state : JointMeasuredMarkedState First) : JointMeasuredMarkedState Last :=
  (state.1.map mapping continuous, mapping ∘ state.2.1,
    fun side => (state.2.2 side).map continuous.measurable.aemeasurable)

/-- Intrinsic joint weak tests are evaluated on the original metric,
physical probability masses, ordered planted marks and whole cadlag path.
Isometric transport makes the evaluation independent of a chosen ambient.
Uniform spatial stability is the bounded-Lipschitz joint GHP test condition. -/
structure IntrinsicJointGHPPathTest where
  bound : ℝ≥0
  spatialLipschitz : ℝ≥0
  value : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space],
    JointMeasuredMarkedState Space → (SkorokhodCadlagPathCompletion Space →ᵇ ℝ)
  bounded : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (state : JointMeasuredMarkedState Space),
    ‖value Space state‖ ≤ bound
  usualContinuity : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (state : JointMeasuredMarkedState Space),
    usualLocalJ1SequentiallyContinuousTest (value Space state)
  spatialStability : ∀ (Space : Type) [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (first last : JointMeasuredMarkedState Space)
    (path : SkorokhodCadlagPathCompletion Space),
    |value Space first path - value Space last path| ≤
      spatialLipschitz * jointMeasuredMarkedStateCost first last
  isometricTransport : ∀ (First Last : Type) [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First] [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last] (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First) (path : SkorokhodCadlagPathCompletion First),
    value Last (jointMeasuredMarkedStateMap mapping isometry.continuous state)
      (skorokhodCadlagContinuousCarrierMapCompletion mapping isometry.continuous path) =
      value First state path

theorem jointMeasuredMarkedStateCost_tendsto_zero
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space]
    (states : ℕ → JointMeasuredMarkedState Space) (state : JointMeasuredMarkedState Space)
    (carrier : Tendsto (fun depth => (states depth).1) atTop (𝓝 state.1))
    (marks : ∀ side, Tendsto (fun depth => (states depth).2.1 side) atTop (𝓝 (state.2.1 side)))
    (masses : ∀ side, Tendsto (fun depth => levyProkhorovEDist
      ((states depth).2.2 side : Measure Space) (state.2.2 side : Measure Space)) atTop (𝓝 0)) :
    Tendsto (fun depth => jointMeasuredMarkedStateCost (states depth) state) atTop (𝓝 0) := by
  have carrierDistance := tendsto_iff_dist_tendsto_zero.mp carrier
  have markDistance : Tendsto (fun depth => ∑ side : Bool,
      dist ((states depth).2.1 side) (state.2.1 side)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun side _ => tendsto_iff_dist_tendsto_zero.mp (marks side))
  have massDistance : Tendsto (fun depth => ∑ side : Bool, levyProkhorovDist
      ((states depth).2.2 side : Measure Space) (state.2.2 side : Measure Space)) atTop (𝓝 0) := by
    have coordinateLimit (side : Bool) : Tendsto (fun depth => levyProkhorovDist
        ((states depth).2.2 side : Measure Space) (state.2.2 side : Measure Space)) atTop (𝓝 0) := by
      simpa only [levyProkhorovDist, ENNReal.toReal_zero, Function.comp_def] using (ENNReal.continuousAt_toReal (by simp : (0 : ENNReal) ≠ ∞)).tendsto.comp (masses side)
    simpa using tendsto_finsetSum Finset.univ (fun side _ => coordinateLimit side)
  simpa only [jointMeasuredMarkedStateCost, add_zero] using (carrierDistance.add markDistance).add massDistance

/-- The genuine quenched marked-GHP data and whole-path weak limit imply
convergence of every intrinsic joint test response in the SAME ambient. -/
theorem intrinsic_joint_test_response_tendsto
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (test : IntrinsicJointGHPPathTest)
    (states : ℕ → JointMeasuredMarkedState Space) (state : JointMeasuredMarkedState Space)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
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
