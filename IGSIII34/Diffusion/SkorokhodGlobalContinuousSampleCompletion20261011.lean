import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion20261011
import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def skorokhodGlobalUnitCoordinateCompletion20261011 (time : ℝ≥0) :
    SkorokhodIntervalTimeCompletion20261011 :=
  ⟨(time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ), by
    have positive : 0 < (⌊(time : ℝ)⌋₊ + 1 : ℝ) := by positivity
    exact ⟨div_nonneg time.property positive.le,
      (div_le_one positive).mpr (Nat.lt_floor_add_one (time : ℝ)).le⟩⟩

def skorokhodGlobalContinuousAssemblyCompletion20261011
    (profiles : ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space)) :
    SkorokhodGlobalPathCompletion20261011 Space :=
  ⟨fun time => profiles ⌊(time : ℝ)⌋₊ (skorokhodGlobalUnitCoordinateCompletion20261011 time)⟩

def skorokhodGlobalProfileSelectionCompletion20261011 (horizon : ℕ)
    (time : SkorokhodIntervalTimeCompletion20261011) : Fin (horizon+2) :=
  ⟨⌊(horizon+1 : ℝ) * (time : ℝ)⌋₊, by
    have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
    have raw := mul_le_mul_of_nonneg_left time.property.2 (by positivity : 0 ≤ (horizon+1 : ℝ))
    rw [realLE] at raw
    have bound : (horizon+1 : ℝ) * (time : ℝ) ≤ (horizon+1 : ℝ) := by
      simpa only [mul_one] using raw
    have floorBound := Nat.floor_mono bound
    have floorCast : ⌊(horizon+1 : ℝ)⌋₊ = horizon+1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (horizon+1)
    rw [floorCast] at floorBound
    omega⟩

def skorokhodGlobalFiniteContinuousAssemblyCompletion20261011 (horizon : ℕ)
    (profiles : Fin (horizon+2) → C(SkorokhodIntervalTimeCompletion20261011, Space)) :
    SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => profiles (skorokhodGlobalProfileSelectionCompletion20261011 horizon time)
    (skorokhodGlobalUnitCoordinateCompletion20261011
      ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))⟩

theorem skorokhodGlobalFiniteContinuousAssembly_lipschitz_completion20261011 (horizon : ℕ) :
    LipschitzWith 1 (skorokhodGlobalFiniteContinuousAssemblyCompletion20261011 (Space := Space) horizon) := by
  apply LipschitzWith.of_edist_le
  intro first second
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  let coordinate := skorokhodGlobalProfileSelectionCompletion20261011 horizon time
  have pointBound : edist
      (first coordinate (skorokhodGlobalUnitCoordinateCompletion20261011
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)))
      (second coordinate (skorokhodGlobalUnitCoordinateCompletion20261011
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))) ≤
      edist (first coordinate) (second coordinate) := by
    rw [ContinuousMap.edist_eq_iSup]
    exact le_iSup (fun point => edist (first coordinate point) (second coordinate point))
      (skorokhodGlobalUnitCoordinateCompletion20261011
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))
  exact pointBound.trans (edist_le_pi_edist first second coordinate)

theorem skorokhodGlobalContinuousAssembly_continuous_completion20261011 :
    Continuous (skorokhodGlobalContinuousAssemblyCompletion20261011 (Space := Space)) := by
  apply skorokhodGlobal_continuous_iff_completion20261011.mpr
  intro horizon
  have identity : (fun profiles => skorokhodIntegerProfileCompletion20261011
      (skorokhodGlobalContinuousAssemblyCompletion20261011 (Space := Space) profiles) horizon) =
      (fun profiles : ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space) =>
        skorokhodGlobalFiniteContinuousAssemblyCompletion20261011 horizon (fun index => profiles index.val)) := by
    funext profiles
    apply congrArg SkorokhodIntervalPathCompletion20261011.mk
    funext time
    simp only [skorokhodGlobalContinuousAssemblyCompletion20261011,
      skorokhodGlobalFiniteContinuousAssemblyCompletion20261011,
      skorokhodGlobalProfileSelectionCompletion20261011, NNReal.coe_mul,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rfl
  rw [identity]
  exact (skorokhodGlobalFiniteContinuousAssembly_lipschitz_completion20261011 horizon).continuous.comp
    (continuous_pi fun index => continuous_apply index.val)

/-- Every continuous full-time sample with measurable evaluations is
Borel measurable in the genuine all-integer-horizon J1 topology. The
proof factors through a countable product of separable continuous-path
spaces, never identifying a nonseparable J1 Borel algebra with a product
sigma algebra. -/
theorem continuousGlobalFamily_measurable_completion20261011
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    Measurable (fun outcome => (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := ⟨rfl⟩
  let profiles : Outcome → ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space) := fun outcome horizon =>
    ⟨fun time => sample outcome ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩),
      (sampleContinuous outcome).comp (by fun_prop)⟩
  have profilesMeasurable : Measurable profiles := by
    apply measurable_pi_lambda
    intro horizon
    apply continuousIntervalFamily_measurable_of_evaluations_completion20261011
    intro time
    exact evaluations ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)
  have assembled := skorokhodGlobalContinuousAssembly_continuous_completion20261011.measurable.comp profilesMeasurable
  convert assembled using 1
  funext outcome
  apply congrArg SkorokhodGlobalPathCompletion20261011.mk
  funext time
  change sample outcome time = sample outcome
    ((⌊(time : ℝ)⌋₊ + 1 : ℝ≥0) *
      ⟨(time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ), _⟩)
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  change (time : ℝ) = (⌊(time : ℝ)⌋₊ + 1 : ℝ) * ((time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ))
  have nonzero : (⌊(time : ℝ)⌋₊ + 1 : ℝ) ≠ 0 := by positivity
  field_simp

def countableSkorokhodGlobalSampleCompletion20261011 (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℕ → Space) : SkorokhodGlobalPathCompletion20261011 Space :=
  ⟨countableTimeContinuousSampleCompletion20261011 times dense sample⟩

theorem countableSkorokhodGlobalSample_measurable_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableSkorokhodGlobalSampleCompletion20261011 (Space := Space) times dense) :=
  continuousGlobalFamily_measurable_completion20261011 _
    (countableTimeContinuousSample_continuous_completion20261011 times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)

end
end IGSIII34.Diffusion
